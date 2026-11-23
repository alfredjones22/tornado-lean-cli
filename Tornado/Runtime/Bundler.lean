import Lean
import Tornado.Domain.NoteIdentity
import Tornado.Protocol.UserOperation08
import Tornado.Runtime.HttpTransport

/-! Bounded ERC-4337 transport. This module owns no note or private key. Its
caller must validate the full withdrawal or deposit policy before approving
the operation. A hash is durably reserved before its only send attempt; all
ambiguous replies remain unknown. No endpoint error text is reflected. -/

namespace Tornado.Runtime.Bundler

open Lean Tornado.Crypto Tornado.Protocol Tornado.Protocol.UserOperation08

def entryPoint : Nat := 0x4337084d9e255ff0702461cf8895ce9e3b5ff108
def maxOperationBytes : Nat := 262144

def quantity (n : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 n)

def dataHex (bytes : ByteArray) : String := "0x" ++ bytesToHex bytes

def address (n : Nat) : Except String String := do
  if n == 0 || n >= 2 ^ 160 then throw "Invalid bundler address."
  return dataHex ((← Abi.addressWord n).extract 12 32)

structure Bounds where
  maxVerificationGas : Nat := 1000000
  maxCallGas : Nat := 8000000
  maxPreVerificationGas : Nat := 1000000
  maxPaymasterVerificationGas : Nat := 2000000
  maxPostOpGas : Nat := 2000000
  maxFeePerGas : Nat := 1000000000000
  maxGasCostWei : Nat := 50000000000000000
  deriving Inhabited

def maximumGasCost (op : UserOperation) : Nat :=
  (op.verificationGasLimit + op.callGasLimit + op.preVerificationGas +
    op.paymasterVerificationGasLimit + op.paymasterPostOpGasLimit) * op.maxFeePerGas

def validate (op : UserOperation) (bounds : Bounds := {}) : Except String Unit := do
  let _ ← address op.sender
  if op.nonce >= 2 ^ 256 || op.callData.size > 131072 ||
      op.factoryData.size > 16384 || op.paymasterData.size > 65536 ||
      op.signature.size > 4096 || op.paymasterSignature.isSome then
    throw "UserOperation exceeds the supported encoding bounds."
  if op.verificationGasLimit == 0 || op.verificationGasLimit > bounds.maxVerificationGas ||
      op.callGasLimit > bounds.maxCallGas || op.preVerificationGas == 0 ||
      op.preVerificationGas > bounds.maxPreVerificationGas ||
      op.paymasterVerificationGasLimit > bounds.maxPaymasterVerificationGas ||
      op.paymasterPostOpGasLimit > bounds.maxPostOpGas ||
      op.maxFeePerGas == 0 || op.maxFeePerGas > bounds.maxFeePerGas ||
      op.maxPriorityFeePerGas > op.maxFeePerGas ||
      maximumGasCost op > bounds.maxGasCostWei then
    throw "UserOperation exceeds the reviewed gas or network fee bounds."
  let _ ← packTransport op

/-- Canonical v0.8 RPC representation. Separate paymaster signatures are
unsupported by this transport policy. -/
def encodeOperation (op : UserOperation) : Except String Json := do
  let mut fields := [
    ("sender", toJson (← address op.sender)), ("nonce", toJson (quantity op.nonce)),
    ("callData", toJson (dataHex op.callData)),
    ("callGasLimit", toJson (quantity op.callGasLimit)),
    ("verificationGasLimit", toJson (quantity op.verificationGasLimit)),
    ("preVerificationGas", toJson (quantity op.preVerificationGas)),
    ("maxFeePerGas", toJson (quantity op.maxFeePerGas)),
    ("maxPriorityFeePerGas", toJson (quantity op.maxPriorityFeePerGas)),
    ("signature", toJson (dataHex op.signature))]
  if let some factory := op.factory then
    let factoryText ← match factory with
      | .eip7702Marker => pure "0x7702"
      | .address value => address value
    fields := fields ++ [("factory", toJson factoryText),
      ("factoryData", toJson (dataHex op.factoryData))]
  if let some paymaster := op.paymaster then
    fields := fields ++ [("paymaster", toJson (← address paymaster)),
      ("paymasterVerificationGasLimit", toJson (quantity op.paymasterVerificationGasLimit)),
      ("paymasterPostOpGasLimit", toJson (quantity op.paymasterPostOpGasLimit)),
      ("paymasterData", toJson (dataHex op.paymasterData))]
  let result := Json.mkObj fields
  if result.compress.toUTF8.size > maxOperationBytes then
    throw "UserOperation JSON exceeds the transport bound."
  return result

structure Authorization where
  chainId : Nat
  delegate : Nat
  nonce : Nat
  r : Nat
  s : Nat
  yParity : Nat
  deriving Inhabited

def authorizationJson (auth : Authorization) : Except String Json := do
  if (auth.chainId != 1 && auth.chainId != 11155111) || auth.nonce >= 2 ^ 64 - 1 ||
      auth.r == 0 || auth.r >= secp256k1Order || auth.s == 0 ||
      auth.s > secp256k1Order / 2 || auth.yParity > 1 then
    throw "Invalid EIP-7702 authorization."
  return Json.mkObj [
    ("chainId", toJson (quantity auth.chainId)),
    ("address", toJson (← address auth.delegate)),
    ("nonce", toJson (quantity auth.nonce)),
    ("r", toJson (dataHex (← Abi.uintWord auth.r))),
    ("s", toJson (dataHex (← Abi.uintWord auth.s))),
    ("yParity", toJson (quantity auth.yParity))]

def withAuthorization (chainId : Nat) (op : UserOperation)
    (auth : Option Authorization) : Except String Json := do
  let json ← encodeOperation op
  match auth with
  | none =>
    if op.authorizationAddress.isSome || op.factory == some .eip7702Marker ||
        op.factory == some (.address markerAddress) then
      throw "EIP-7702 operation is missing its authorization."
    return json
  | some authorization =>
    let marked := op.factory == some .eip7702Marker ||
      op.factory == some (.address markerAddress)
    let deploymentMatches := if marked then
      op.authorizationAddress == some authorization.delegate
      else op.factory.isNone && op.authorizationAddress.isNone
    if authorization.chainId != chainId || !deploymentMatches ||
        authorization.delegate != 0xe6cae83bde06e4c305530e199d7217f42808555b then
      throw "Authorization differs from the reviewed operation network or delegate."
    return json.setObjVal! "eip7702Auth" (← authorizationJson authorization)

structure GasEstimate where
  verificationGasLimit : Nat
  callGasLimit : Nat
  preVerificationGas : Nat
  paymasterVerificationGasLimit : Nat
  paymasterPostOpGasLimit : Nat
  deriving Inhabited

private def gasField (json : Json) (key : String) : Except String Nat := do
  JsonRpc.parseHexQuantity (← (← json.getObjVal? key).getStr?)

/-- Missing paymaster fields retain the local baseline, never zero it. -/
def parseEstimate (json : Json) (baseline : UserOperation)
    (bounds : Bounds := {}) : Except String GasEstimate := do
  if json.compress.toUTF8.size > 4096 then throw "Oversized bundler gas estimate."
  let optional (key : String) (fallback : Nat) : Except String Nat :=
    if (json.getObjVal? key).isOk then gasField json key else .ok fallback
  let gas : GasEstimate := {
    verificationGasLimit := ← gasField json "verificationGasLimit"
    callGasLimit := ← gasField json "callGasLimit"
    preVerificationGas := ← gasField json "preVerificationGas"
    paymasterVerificationGasLimit := ← optional "paymasterVerificationGasLimit"
      baseline.paymasterVerificationGasLimit
    paymasterPostOpGasLimit := ← optional "paymasterPostOpGasLimit"
      baseline.paymasterPostOpGasLimit }
  validate { baseline with
    verificationGasLimit := gas.verificationGasLimit,
    callGasLimit := gas.callGasLimit, preVerificationGas := gas.preVerificationGas,
    paymasterVerificationGasLimit := gas.paymasterVerificationGasLimit,
    paymasterPostOpGasLimit := gas.paymasterPostOpGasLimit } bounds
  return gas

private def checked (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

def parseHash (json : Json) : Except String ByteArray := do
  let raw ← json.getStr?
  if raw.length != 66 || !raw.startsWith "0x" then throw "Invalid operation hash."
  let bytes ← Tornado.Domain.parseHexBytes raw
  if bytes.size != 32 then throw "Invalid operation hash."
  return bytes

structure Effects where
  rpc : JsonRpc.Method → Array Json → IO Json
  reserve : ByteArray → ByteArray → IO Unit
  markExposed : ByteArray → IO Unit
  markSubmitted : ByteArray → IO Unit
  markUnknown : ByteArray → IO Unit

inductive Outcome where
  | submitted (hash : ByteArray)
  | unknown (hash : ByteArray)
  deriving Inhabited

/-- Reservation and exposure must be durable before a signed payload can
leave the process. A failed send or contradictory reply is never retried.
The callbacks must implement protected exclusive/CAS journal transitions. -/
def submitWith (effects : Effects) (chainId : Nat) (op : UserOperation)
    (bounds : Bounds := {}) (authorization : Option Authorization := none) : IO Outcome := do
  if chainId != 1 && chainId != 11155111 then
    throw <| IO.userError "Unsupported bundler network."
  let _ ← checked (validate op bounds)
  if op.signature.size != 65 then
    throw <| IO.userError "A final UserOperation requires a canonical owner signature."
  let hash ← checked (userOperationHash chainId entryPoint op)
  let json ← checked (withAuthorization chainId op authorization)
  let bytes := json.compress.toUTF8
  effects.reserve hash bytes
  effects.markExposed hash
  try
    let reply ← effects.rpc .sendUserOperation
      #[json, toJson (← checked (address entryPoint))]
    if (← checked (parseHash reply)) != hash then
      throw <| IO.userError "Bundler returned a different operation hash."
    effects.markSubmitted hash
    return .submitted hash
  catch _ =>
    try effects.markUnknown hash catch _ => pure ()
    return .unknown hash

end Tornado.Runtime.Bundler
