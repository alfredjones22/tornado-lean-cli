import Tornado.Protocol.Abi
import Tornado.Crypto.Secp256k1

/-!
EntryPoint v0.8 `PackedUserOperation` EIP-712 hashing, implemented in Lean.
This matches the pinned viem 2.55.19 packing and hash path. It is a pure
protocol primitive: it does not validate a Tornado proof, estimate gas,
reserve a note, sign a real transaction, or contact a bundler.
-/

namespace Tornado.Protocol.UserOperation08

open Tornado.Crypto Tornado.Protocol.Abi

def maxUint128 : Nat := 2 ^ 128
def maxSignatureLength : Nat := 2 ^ 16
def paymasterSignatureMagic : ByteArray :=
  ByteArray.mk #[0x22, 0xe3, 0x25, 0xa2, 0x97, 0x43, 0x96, 0x56]

/-- The short 7702 factory marker and its padded address form share the
    `forHash` behavior in viem's `getInitCode`. -/
def markerAddress : Nat := 0x7702000000000000000000000000000000000000

inductive Factory where
  | address (value : Nat)
  | eip7702Marker
  deriving Inhabited, BEq

structure UserOperation where
  sender : Nat
  nonce : Nat := 0
  factory : Option Factory := none
  factoryData : ByteArray := ByteArray.empty
  authorizationAddress : Option Nat := none
  callData : ByteArray := ByteArray.empty
  verificationGasLimit : Nat := 0
  callGasLimit : Nat := 0
  preVerificationGas : Nat := 0
  maxPriorityFeePerGas : Nat := 0
  maxFeePerGas : Nat := 0
  paymaster : Option Nat := none
  paymasterVerificationGasLimit : Nat := 0
  paymasterPostOpGasLimit : Nat := 0
  paymasterData : ByteArray := ByteArray.empty
  paymasterSignature : Option ByteArray := none
  signature : ByteArray := ByteArray.empty
  deriving Inhabited

structure PackedOperation where
  sender : Nat
  nonce : Nat
  initCode : ByteArray
  callData : ByteArray
  accountGasLimits : ByteArray
  preVerificationGas : Nat
  gasFees : ByteArray
  paymasterAndData : ByteArray
  signature : ByteArray
  deriving Inhabited

private def natBytesBE (n count : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:count] do
    result := result.push ((n / 2 ^ (8 * (count - 1 - i)) % 256).toUInt8)
  return result

private def addressBytes (address : Nat) : Except String ByteArray := do
  if address >= maxAddress then throw "UserOperation address is out of range."
  return natBytesBE address 20

/-- Strict big-endian uint128 field; viem's 16-byte padding rejects overflow. -/
def uint128Bytes (value : Nat) : Except String ByteArray := do
  if value >= maxUint128 then throw "UserOperation uint128 gas value is out of range."
  return natBytesBE value 16

def packUint128Pair (high low : Nat) : Except String ByteArray := do
  return (← uint128Bytes high) ++ (← uint128Bytes low)

private def markerInitCode (operation : UserOperation) : Except String ByteArray := do
  match operation.authorizationAddress with
  | none => addressBytes markerAddress
  | some address => return (← addressBytes address) ++ operation.factoryData

/-- The exact `forHash: true` initCode rule for EntryPoint v0.8, including
    EIP-7702's special factory marker and authorization substitution. -/
def initCodeForHash (operation : UserOperation) : Except String ByteArray := do
  match operation.factory with
  | none => return ByteArray.empty
  | some .eip7702Marker => markerInitCode operation
  | some (.address factory) =>
      if factory == markerAddress then markerInitCode operation
      else return (← addressBytes factory) ++ operation.factoryData

/-- Wire form preserves the caller's actual factory bytes. A short `0x7702`
    marker stays two bytes; a padded marker stays twenty bytes. -/
def initCodeTransport (operation : UserOperation) : Except String ByteArray := do
  match operation.factory with
  | none => return ByteArray.empty
  | some .eip7702Marker => return ByteArray.mk #[0x77, 0x02] ++ operation.factoryData
  | some (.address factory) =>
      return (← addressBytes factory) ++ operation.factoryData

/-- Shared paymaster prefix before any optional signature trailer. -/
private def paymasterPrefix (operation : UserOperation) : Except String ByteArray := do
  match operation.paymaster with
  | none => return ByteArray.empty
  | some paymaster =>
      return (← addressBytes paymaster) ++
        (← packUint128Pair operation.paymasterVerificationGasLimit operation.paymasterPostOpGasLimit) ++
        operation.paymasterData

/-- `forHash: true` paymaster data. Viem appends the eight-byte magic when a
    separate paymaster signature exists, while excluding the signature bytes. -/
def paymasterAndData (operation : UserOperation) : Except String ByteArray := do
  match operation.paymaster with
  | none => return ByteArray.empty
  | some _ =>
      let baseData ← paymasterPrefix operation
      return baseData ++ (if operation.paymasterSignature.isSome then
        paymasterSignatureMagic else ByteArray.empty)

/-- Transport form: signature bytes, uint16 big-endian length, then magic.
    This codec does not apply the effectful caller's transport policy. -/
def paymasterAndDataTransport (operation : UserOperation) : Except String ByteArray := do
  match operation.paymaster with
  | none => return ByteArray.empty
  | some _ =>
      let baseData ← paymasterPrefix operation
      match operation.paymasterSignature with
      | none => return baseData
      | some signature =>
          if signature.size >= maxSignatureLength then
            throw "Paymaster signature exceeds uint16 length."
          return baseData ++ signature ++ natBytesBE signature.size 2 ++
            paymasterSignatureMagic

/-- Pure v0.8 packing. Signature is retained for transport parity but is not
    part of the EIP-712 struct hash. -/
def pack (operation : UserOperation) : Except String PackedOperation := do
  let _ ← addressWord operation.sender
  let _ ← uintWord operation.nonce
  let _ ← uintWord operation.preVerificationGas
  return {
    sender := operation.sender,
    nonce := operation.nonce,
    initCode := (← initCodeForHash operation),
    callData := operation.callData,
    accountGasLimits := (← packUint128Pair operation.verificationGasLimit operation.callGasLimit),
    preVerificationGas := operation.preVerificationGas,
    gasFees := (← packUint128Pair operation.maxPriorityFeePerGas operation.maxFeePerGas),
    paymasterAndData := (← paymasterAndData operation),
    signature := operation.signature
  }

/-- The non-hash packed form used by the wire transport. -/
def packTransport (operation : UserOperation) : Except String PackedOperation := do
  let packed ← pack operation
  return { packed with initCode := (← initCodeTransport operation), paymasterAndData := (← paymasterAndDataTransport operation) }

/-- ERC-4337 v0.8 uses EIP-712 domain name `ERC4337`, version `1`. -/
def domainHash (chainId entryPoint : Nat) : Except String ByteArray := do
  let encoded :=
    keccak256 "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)".toUTF8 ++
    keccak256 "ERC4337".toUTF8 ++ keccak256 "1".toUTF8 ++
    (← uintWord chainId) ++ (← addressWord entryPoint)
  return keccak256 encoded

/-- The eight-field v0.8 packed struct hash, with dynamic bytes hashed once. -/
def messageHash (packed : PackedOperation) : Except String ByteArray := do
  if packed.accountGasLimits.size != 32 || packed.gasFees.size != 32 then
    throw "Packed UserOperation gas fields must be bytes32."
  let encoded :=
    keccak256 "PackedUserOperation(address sender,uint256 nonce,bytes initCode,bytes callData,bytes32 accountGasLimits,uint256 preVerificationGas,bytes32 gasFees,bytes paymasterAndData)".toUTF8 ++
    (← addressWord packed.sender) ++ (← uintWord packed.nonce) ++
    keccak256 packed.initCode ++ keccak256 packed.callData ++
    packed.accountGasLimits ++ (← uintWord packed.preVerificationGas) ++
    packed.gasFees ++ keccak256 packed.paymasterAndData
  return keccak256 encoded

/-- This is viem's `getUserOperationHash` for EntryPoint version `0.8`.
    Unlike v0.6/v0.7, it is the EIP-712 digest directly. -/
def userOperationHash (chainId entryPoint : Nat) (operation : UserOperation) : Except String ByteArray := do
  let domain ← domainHash chainId entryPoint
  -- The transport signature is not part of the v0.8 EIP-712 message.
  let normalized := { operation with signature := ByteArray.empty }
  let message ← messageHash (← pack normalized)
  return keccak256 (ByteArray.mk #[0x19, 0x01] ++ domain ++ message)

/-- Deterministic low-S owner signature over the exact v0.8 typed-data digest.
    The current pure Lean secp256k1 arithmetic is variable-time. -/
def signUserOperation (privateKey : ByteArray) (chainId entryPoint : Nat)
    (operation : UserOperation) : Except String ByteArray := do
  let digest ← userOperationHash chainId entryPoint operation
  return (← secp256k1SignDigest privateKey digest).bytes65

/-- Signature bytes do not enter the v0.8 typed-data digest. This is a
    structural fact about the native encoder, not a cryptographic theorem. -/
theorem hash_ignores_signature (chainId entryPoint : Nat) (operation : UserOperation)
    (replacement : ByteArray) :
    userOperationHash chainId entryPoint { operation with signature := replacement } =
      userOperationHash chainId entryPoint operation := by
  cases operation
  rfl

/-- When a separate paymaster signature is present, its bytes do not change
    the typed-data hash; the magic marker does. -/
theorem hash_ignores_paymaster_signature_bytes (chainId entryPoint : Nat)
    (operation : UserOperation) (left right : ByteArray) :
    userOperationHash chainId entryPoint
      { operation with paymasterSignature := some left } =
    userOperationHash chainId entryPoint
      { operation with paymasterSignature := some right } := by
  cases operation
  rfl

/-- No paymaster makes the packed paymaster bytes empty, as in viem. -/
theorem no_paymaster_has_empty_data (operation : UserOperation)
    (h : operation.paymaster = none) :
    paymasterAndData operation = .ok ByteArray.empty := by
  simp [paymasterAndData, h]
  rfl

/-- A gas value outside uint128 is rejected before any byte truncation. -/
theorem uint128_overflow_rejected (value : Nat) (h : maxUint128 ≤ value) :
    uint128Bytes value = .error "UserOperation uint128 gas value is out of range." := by
  simp [uint128Bytes, h]
  rfl

end Tornado.Protocol.UserOperation08

#print axioms Tornado.Protocol.UserOperation08.hash_ignores_signature
#print axioms Tornado.Protocol.UserOperation08.hash_ignores_paymaster_signature_bytes
#print axioms Tornado.Protocol.UserOperation08.no_paymaster_has_empty_data
#print axioms Tornado.Protocol.UserOperation08.uint128_overflow_rejected
