import Tornado.Crypto.Keccak

/-!
Pure native Lean RLP and typed transaction encoding for the ordinary EIP-1559
deposit/recovery route, plus the EIP-7702 authorization preimage. This module
does not sign, write a journal, contact a node, or submit a transaction.
-/

namespace Tornado.Protocol.Rlp

open Tornado.Crypto

def maxUint256 : Nat := 2 ^ 256
def maxAddress : Nat := 2 ^ 160

private def natBytesBE (value count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push ((value / 256 ^ (count - 1 - i) % 256).toUInt8)
  return bytes

/-- Minimal unsigned big-endian representation; zero is the empty byte string. -/
def minimalNatBytes (value : Nat) : ByteArray :=
  if value == 0 then ByteArray.empty
  else natBytesBE value (value.log2 / 8 + 1)

private def lengthPrefix (base length : Nat) : ByteArray :=
  if length <= 55 then ByteArray.empty.push (base + length).toUInt8
  else
    let lengthBytes := minimalNatBytes length
    (ByteArray.empty.push (base + 55 + lengthBytes.size).toUInt8) ++ lengthBytes

/-- Canonical RLP byte-string encoding. -/
def bytes (value : ByteArray) : ByteArray :=
  if value.size == 1 && (value.get! 0).toNat < 0x80 then value
  else lengthPrefix 0x80 value.size ++ value

/-- Canonical RLP list encoding from already RLP-encoded child items. -/
def list (children : List ByteArray) : ByteArray :=
  let payload := children.foldl (· ++ ·) ByteArray.empty
  lengthPrefix 0xc0 payload.size ++ payload

/-- Unsigned integer as an RLP byte string. -/
def nat (value : Nat) : ByteArray := bytes (minimalNatBytes value)

structure AccessEntry where
  address : Nat
  storageKeys : Array ByteArray
  deriving Inhabited

structure Transaction1559 where
  chainId : Nat
  nonce : Nat
  maxPriorityFeePerGas : Nat
  maxFeePerGas : Nat
  gas : Nat
  to : Option Nat := none
  value : Nat
  data : ByteArray := ByteArray.empty
  accessList : Array AccessEntry := #[]
  deriving Inhabited

structure Signature where
  yParity : Nat
  r : Nat
  s : Nat
  deriving Inhabited

private def addressBytes (address : Nat) : Except String ByteArray := do
  if address >= maxAddress then throw "Address is outside uint160."
  return natBytesBE address 20

/-- Values are bounded to the fields accepted by Ethereum transactions; fee
    ordering is checked before serialization. -/
def validateTransaction (tx : Transaction1559) : Except String Unit := do
  if tx.chainId == 0 || tx.chainId >= maxUint256 then throw "Invalid EIP-1559 chain ID."
  if tx.nonce >= maxUint256 || tx.maxPriorityFeePerGas >= maxUint256 ||
      tx.maxFeePerGas >= maxUint256 || tx.gas >= maxUint256 ||
      tx.value >= maxUint256 then throw "EIP-1559 uint256 field is out of range."
  if tx.maxPriorityFeePerGas > tx.maxFeePerGas then
    throw "EIP-1559 priority fee exceeds max fee."
  if let some recipient := tx.to then
    let _ ← addressBytes recipient
  for entry in tx.accessList do
    let _ ← addressBytes entry.address
    for key in entry.storageKeys do
      if key.size != 32 then throw "EIP-1559 access-list key must be bytes32."

private def accessListItem (entries : Array AccessEntry) : Except String ByteArray := do
  let mut items : List ByteArray := []
  for entry in entries do
    let address ← addressBytes entry.address
    let keys := list (entry.storageKeys.toList.map bytes)
    items := items ++ [list [bytes address, keys]]
  return list items

private def signatureItems (sig : Signature) : Except String (List ByteArray) := do
  if sig.yParity > 1 || sig.r == 0 || sig.s == 0 ||
      sig.r >= maxUint256 || sig.s >= maxUint256 then
    throw "Invalid EIP-1559 signature fields."
  return [nat sig.yParity, nat sig.r, nat sig.s]

/-- EIP-1559 envelope, unsigned when no signature is supplied. The unsigned
    envelope is the ECDSA signing preimage. -/
def serialize1559 (tx : Transaction1559) (signature : Option Signature := none) : Except String ByteArray := do
  validateTransaction tx
  let recipient ← match tx.to with
    | none => pure ByteArray.empty
    | some address => addressBytes address
  let base : List ByteArray := [
    nat tx.chainId, nat tx.nonce, nat tx.maxPriorityFeePerGas,
    nat tx.maxFeePerGas, nat tx.gas, bytes recipient, nat tx.value,
    bytes tx.data, (← accessListItem tx.accessList)
  ]
  let suffix ← match signature with
    | none => pure []
    | some sig => signatureItems sig
  return (ByteArray.empty.push 0x02) ++ list (base ++ suffix)

def signingHash1559 (tx : Transaction1559) : Except String ByteArray :=
  (serialize1559 tx none).map keccak256

def transactionHash1559 (tx : Transaction1559) (sig : Signature) : Except String ByteArray :=
  (serialize1559 tx (some sig)).map keccak256

/-- EIP-7702 authorization hash: keccak256(0x05 || RLP([chainId,address,nonce])). -/
def authorizationHash7702 (chainId address nonce : Nat) : Except String ByteArray := do
  if chainId >= maxUint256 || nonce >= maxUint256 then
    throw "EIP-7702 authorization integer is out of range."
  let address ← addressBytes address
  return keccak256 ((ByteArray.empty.push 0x05) ++
    list [nat chainId, bytes address, nat nonce])

/-- Every serialized EIP-1559 transaction has a nonzero chain ID because
    the serializer invokes the same checked native predicate. -/
theorem zero_chain_id_rejected (tx : Transaction1559) (sig : Option Signature) (h : tx.chainId = 0) :
    (serialize1559 tx sig).isOk = false := by
  simp [serialize1559, validateTransaction, h, bind, Except.bind]
  rfl

/-- Authorization encodings reject addresses outside uint160. -/
theorem authorization_address_bound (chainId address nonce : Nat)
    (h : address >= maxAddress) :
    (authorizationHash7702 chainId address nonce).isOk = false := by
  by_cases hc : chainId >= maxUint256 || nonce >= maxUint256
  · simp [authorizationHash7702, hc, bind, Except.bind]
    rfl
  · simp [authorizationHash7702, addressBytes, h, hc, bind, Except.bind]
    rfl

/-- RLP zero is the canonical empty-string encoding. -/
theorem rlp_zero : nat 0 = ByteArray.mk #[0x80] := by
  decide

end Tornado.Protocol.Rlp

#print axioms Tornado.Protocol.Rlp.zero_chain_id_rejected
#print axioms Tornado.Protocol.Rlp.authorization_address_bound
#print axioms Tornado.Protocol.Rlp.rlp_zero
