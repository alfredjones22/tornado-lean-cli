import Tornado.Protocol.SagaHistory

/-!
Bounded pure Ethereum JSON-RPC history response validator. An RPC response is
still a provider claim: syntax, chain identity, pool identity, range and event
shape can be checked, but omitted logs cannot be detected without an
independent authenticated chain source.
-/

namespace Tornado.Protocol.RpcHistory

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol.Events
open Tornado.Protocol.SagaHistory

def maxRpcResponseBytes : Nat := 1024 * 1024
def maxRpcBlocks : Nat := 1000
def maxRpcLogs : Nat := 10000

structure CheckedSlice where
  fromBlock : Nat
  toBlock : Nat
  events : Array ValidatedEvent
  deriving Inhabited

private def invalid : String := "Invalid pool history RPC response."

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name |>.mapError (fun _ => invalid)

private def string (json : Json) (name : String) : Except String String := do
  (← field json name).getStr? |>.mapError (fun _ => invalid)

private def quantity (json : Json) (name : String) : Except String Nat :=
  (string json name).bind Tornado.Runtime.JsonRpc.parseHexQuantity

private def fixedHex (raw : String) (width : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw invalid
  let bytes ← parseHexBytes raw
  if bytes.size != width then throw invalid
  return bytes

private def address (raw : String) : Except String Nat := do
  let bytes ← fixedHex raw 20
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def quantityHex (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def addressHex (value : Nat) : String := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:20] do
    bytes := bytes.push (UInt8.ofNat ((value / (256 ^ (19 - i))) % 256))
  return "0x" ++ bytesToHex bytes

/-- Construct one bounded, exact-pool `eth_getLogs` filter. The caller passes
    this array to `JsonRpc.encodeRequest` with method `.getLogs`. -/
def permittedRange (selection : Selection) (fromBlock toBlock : Nat) : Bool :=
  selection.pool < 2 ^ 160 && selection.registeredBlock ≤ fromBlock &&
  fromBlock ≤ toBlock && toBlock ≤ selection.head &&
  toBlock - fromBlock < maxRpcBlocks

def requestParams (selection : Selection) (fromBlock toBlock : Nat) :
    Except String (Array Json) :=
  if permittedRange selection fromBlock toBlock then .ok #[Json.mkObj [
    ("address", toJson (addressHex selection.pool)),
    ("fromBlock", toJson (quantityHex fromBlock)),
    ("toBlock", toJson (quantityHex toBlock))]]
  else .error "Invalid RPC history range."

theorem request_params_sound (selection : Selection) (fromBlock toBlock : Nat)
    (params : Array Json)
    (h : requestParams selection fromBlock toBlock = .ok params) :
    permittedRange selection fromBlock toBlock = true := by
  by_cases hr : permittedRange selection fromBlock toBlock = true
  · exact hr
  · simp [requestParams, hr] at h

private def decodeLog (selection : Selection) (fromBlock toBlock : Nat)
    (json : Json) : Except String ValidatedEvent := do
  let blockNumber ← quantity json "blockNumber"
  let logIndex ← quantity json "logIndex"
  let _ ← quantity json "transactionIndex"
  if blockNumber < fromBlock || blockNumber > toBlock then throw invalid
  let emitter ← address (← string json "address")
  if emitter != selection.pool then throw invalid
  let _ ← fixedHex (← string json "blockHash") 32
  let _ ← fixedHex (← string json "transactionHash") 32
  if let .ok removed := json.getObjVal? "removed" then
    if (← removed.getBool? |>.mapError (fun _ => invalid)) then throw invalid
  let rawTopics ← (← field json "topics").getArr? |>.mapError (fun _ => invalid)
  let topics ← rawTopics.mapM fun item => do
    let text ← item.getStr? |>.mapError (fun _ => invalid)
    fixedHex text 32
  let rawData ← string json "data"
  if !rawData.startsWith "0x" then throw invalid
  let data ← parseHexBytes rawData
  if data.size > 1024 * 1024 then throw invalid
  let log : Log := { address := emitter, topics, data }
  if topics[0]? == some depositTopic then
    let _ ← decodeDeposit log
    return { blockNumber, logIndex, log, isDeposit := true }
  if topics[0]? == some withdrawalTopic then
    let _ ← decodeWithdrawal log
    return { blockNumber, logIndex, log, isDeposit := false }
  throw "Unsupported pool event in RPC history."

/-- Validate the chain-ID and log envelopes from the same configured RPC
    endpoint, then every returned log. Empty results are accepted as provider
    claims; they do not prove that the range had no events. -/
def parseRange (selection : Selection) (fromBlock toBlock : Nat)
    (chainRequestId logsRequestId : Nat) (chainResponse logsResponse : String) :
    Except String CheckedSlice := do
  let _ ← requestParams selection fromBlock toBlock
  if chainResponse.toUTF8.size > maxRpcResponseBytes ||
      logsResponse.toUTF8.size > maxRpcResponseBytes then
    throw "RPC history response exceeds one MiB."
  let chainJson ← Tornado.Runtime.JsonRpc.parseResult chainRequestId chainResponse
  let chain ← Tornado.Runtime.JsonRpc.parseHexQuantity
    (← chainJson.getStr? |>.mapError (fun _ => invalid))
  if chain != selection.chainId then throw "RPC history chain ID mismatch."
  let logsJson ← Tornado.Runtime.JsonRpc.parseResult logsRequestId logsResponse
  let rawLogs ← logsJson.getArr? |>.mapError (fun _ => invalid)
  if rawLogs.size > maxRpcLogs then throw "RPC history has too many logs."
  let mut previous : Option (Nat × Nat) := none
  let mut events := #[]
  for raw in rawLogs do
    let event ← decodeLog selection fromBlock toBlock raw
    if let some (block, index) := previous then
      if event.blockNumber < block ||
          (event.blockNumber == block && event.logIndex ≤ index) then
        throw "RPC history logs are not strictly ordered."
    previous := some (event.blockNumber, event.logIndex)
    events := events.push event
  return { fromBlock, toBlock, events }

end Tornado.Protocol.RpcHistory

#print axioms Tornado.Protocol.RpcHistory.request_params_sound
