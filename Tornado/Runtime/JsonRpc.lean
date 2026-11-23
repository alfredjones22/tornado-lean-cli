import Lean

/-!
Pure JSON-RPC 2.0 request and response boundary for the eventual native chain
transport. Transport, TLS authentication, chain consensus and finality remain
outside this module. No network request is made here.
-/

namespace Tornado.Runtime.JsonRpc

open Lean

inductive Method where
  | chainId | blockNumber | getBlockByNumber | getCode | getBalance
  | getStorageAt | getTransactionCount | call | estimateGas | feeHistory
  | getLogs | getTransactionByHash | getTransactionReceipt | sendRawTransaction
  | estimateUserOperationGas | sendUserOperation | getUserOperationReceipt
  | getUserOperationByHash
  | pimlicoGasPrice
  | gasPrice
  | maxPriorityFee
  | simulateV1
  deriving Repr, BEq, DecidableEq

def Method.text : Method → String
  | .chainId => "eth_chainId"
  | .blockNumber => "eth_blockNumber"
  | .getBlockByNumber => "eth_getBlockByNumber"
  | .getCode => "eth_getCode"
  | .getBalance => "eth_getBalance"
  | .getStorageAt => "eth_getStorageAt"
  | .getTransactionCount => "eth_getTransactionCount"
  | .call => "eth_call"
  | .estimateGas => "eth_estimateGas"
  | .feeHistory => "eth_feeHistory"
  | .getLogs => "eth_getLogs"
  | .getTransactionByHash => "eth_getTransactionByHash"
  | .getTransactionReceipt => "eth_getTransactionReceipt"
  | .sendRawTransaction => "eth_sendRawTransaction"
  | .estimateUserOperationGas => "eth_estimateUserOperationGas"
  | .sendUserOperation => "eth_sendUserOperation"
  | .getUserOperationReceipt => "eth_getUserOperationReceipt"
  | .getUserOperationByHash => "eth_getUserOperationByHash"
  | .pimlicoGasPrice => "pimlico_getUserOperationGasPrice"
  | .gasPrice => "eth_gasPrice"
  | .maxPriorityFee => "eth_maxPriorityFeePerGas"
  | .simulateV1 => "eth_simulateV1"

/-- The method is an enum so a caller cannot smuggle an arbitrary JSON-RPC
    method name into a fund-sensitive flow. IDs are restricted to the range
    represented exactly by JavaScript's Number for oracle interoperability. -/
def encodeRequest (id : Nat) (method : Method) (params : Array Json) : Except String String := do
  if id > 9007199254740991 then
    throw "JSON-RPC request ID exceeds the safe integer range."
  return (Json.mkObj [
    ("jsonrpc", toJson ("2.0" : String)),
    ("id", toJson id),
    ("method", toJson method.text),
    ("params", Json.arr params)]).compress

/-- Strict envelope check. It rejects a mismatched ID, absent version, a
    result/error collision, and malformed error details. A successful return
    is still only a claim from an unauthenticated JSON value. -/
def decodeResult (expectedId : Nat) (json : Json) : Except String Json := do
  let version ← (← json.getObjVal? "jsonrpc").getStr?
  if version != "2.0" then throw "Unexpected JSON-RPC version."
  let id ← (← json.getObjVal? "id").getNat?
  if id != expectedId then throw "JSON-RPC response ID differs from the request."
  let result := json.getObjVal? "result"
  let remoteError := json.getObjVal? "error"
  if result.isOk && remoteError.isOk then
    throw "JSON-RPC response contains both a result and an error."
  if let .ok error := remoteError then
    let code ← (← error.getObjVal? "code").getInt?
    let message ← (← error.getObjVal? "message").getStr?
    throw s!"JSON-RPC {code}: {message}"
  match result with
  | .error _ => throw "JSON-RPC response has no result."
  | .ok value => return value

def parseResult (expectedId : Nat) (raw : String) : Except String Json := do
  decodeResult expectedId (← Json.parse raw)

inductive Reply where
  | success (result : Json)
  | failure (code : Int) (message : String) (data : Option Json := none)

/-- Structured errors are retained only for bounded, local classification.
Callers must never reflect a remote message or request body to the terminal. -/
def parseReply (expectedId : Nat) (raw : String) : Except String Reply := do
  if raw.utf8ByteSize > 1024 * 1024 then throw "Oversized JSON-RPC reply."
  let json ← Json.parse raw |>.mapError (fun _ => "Invalid JSON-RPC reply.")
  if (← (← json.getObjVal? "jsonrpc").getStr?) != "2.0" ||
      (← (← json.getObjVal? "id").getNat?) != expectedId then
    throw "Mismatched JSON-RPC reply envelope."
  let result := json.getObjVal? "result"
  let failure := json.getObjVal? "error"
  if result.isOk == failure.isOk then throw "Invalid JSON-RPC result/error shape."
  if let .ok value := result then return .success value
  let error ← failure
  let code ← (← error.getObjVal? "code").getInt?
  let message ← (← error.getObjVal? "message").getStr?
  if code < -(2 ^ 31 : Int) || code >= (2 ^ 31 : Int) || message.utf8ByteSize > 4096 then
    throw "JSON-RPC error exceeds the supported bound."
  return .failure code message (error.getObjVal? "data").toOption

private def hexDigit (digit : Char) : Option Nat :=
  if '0' ≤ digit && digit ≤ '9' then some (digit.toNat - '0'.toNat)
  else if 'a' ≤ digit && digit ≤ 'f' then some (digit.toNat - 'a'.toNat + 10)
  else none

/-- EIP-1474 canonical quantity syntax, bounded to uint256. Rejecting
    leading zeros and upper-case digits prevents ambiguous encodings. -/
def parseHexQuantity (raw : String) : Except String Nat := do
  if !raw.startsWith "0x" then throw "RPC quantity must start with 0x."
  let digits := raw.toList.drop 2
  if digits.isEmpty || (digits.length > 1 && digits.head? == some '0') then
    throw "RPC quantity is empty or has leading zeros."
  if digits.length > 64 then throw "RPC quantity exceeds uint256."
  let mut value := 0
  for digit in digits do
    let some nibble := hexDigit digit
      | throw "RPC quantity has a noncanonical hex digit."
    value := value * 16 + nibble
  return value

def parseQuantityResult (expectedId : Nat) (raw : String) : Except String Nat := do
  let value ← parseResult expectedId raw
  parseHexQuantity (← value.getStr?)

end Tornado.Runtime.JsonRpc
