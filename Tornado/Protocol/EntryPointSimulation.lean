import Tornado.Runtime.Bundler
import Tornado.Protocol.Events

/-! Pure encoding and validation for the signed EntryPoint simulation. The
request contains an executable operation and must only be exposed after a
durable candidate reservation. No network effect is performed here. -/

namespace Tornado.Protocol.EntryPointSimulation

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08

def simulator : Nat := 0xdead

/-- Exact ABI for one PackedUserOperation in EntryPoint.handleOps. Dynamic
offsets are measured from the start of the nine-word tuple head. -/
def handleOpsData (op : UserOperation) : Except String ByteArray := do
  let packed ← packTransport op
  let init ← Abi.dynamicBytes packed.initCode
  let calls ← Abi.dynamicBytes packed.callData
  let paymaster ← Abi.dynamicBytes packed.paymasterAndData
  let signature ← Abi.dynamicBytes packed.signature
  let head := (← Abi.addressWord packed.sender) ++ (← Abi.uintWord packed.nonce) ++
    (← Abi.uintWord 288) ++ (← Abi.uintWord (288 + init.size)) ++
    packed.accountGasLimits ++ (← Abi.uintWord packed.preVerificationGas) ++
    packed.gasFees ++ (← Abi.uintWord (288 + init.size + calls.size)) ++
    (← Abi.uintWord (288 + init.size + calls.size + paymaster.size))
  return Abi.selector
    "handleOps((address,uint256,bytes,bytes,bytes32,uint256,bytes32,bytes,bytes)[],address)" ++
    (← Abi.uintWord 64) ++ (← Abi.addressWord simulator) ++
    (← Abi.uintWord 1) ++ (← Abi.uintWord 32) ++ head ++
    init ++ calls ++ paymaster ++ signature

def gasLimit (op : UserOperation) : Nat :=
  op.verificationGasLimit + op.callGasLimit + op.preVerificationGas +
    op.paymasterVerificationGasLimit + op.paymasterPostOpGasLimit + 1000000

def requestParams (op : UserOperation) (bounds : Bundler.Bounds := {}) : Except String (Array Json) := do
  Bundler.validate op bounds
  if op.signature.size != 65 || op.authorizationAddress.isSome then
    throw "Signed account simulation requires a final SimpleAccount operation."
  let simulatorAddress ← Bundler.address simulator
  let target ← Bundler.address Bundler.entryPoint
  let call := Json.mkObj [("from", toJson simulatorAddress), ("to", toJson target),
    ("data", toJson (Bundler.dataHex (← handleOpsData op))),
    ("gas", toJson (Bundler.quantity (gasLimit op)))]
  let overrides := Json.mkObj [(simulatorAddress, Json.mkObj [
    ("balance", toJson (Bundler.quantity (10 ^ 30)))])]
  return #[Json.mkObj [
    ("blockStateCalls", Json.arr #[Json.mkObj [
      ("stateOverrides", overrides), ("calls", Json.arr #[call])]]),
    ("traceTransfers", toJson true), ("validation", toJson false),
    ("returnFullTransactions", toJson false)], toJson ("latest" : String)]

private def field (json : Json) (key : String) : Except String Json := json.getObjVal? key

private def quantity (json : Json) : Except String Nat := do
  JsonRpc.parseHexQuantity (← json.getStr?)

private def data (json : Json) (maxBytes : Nat) : Except String ByteArray := do
  let text ← json.getStr?
  if !text.startsWith "0x" || text.utf8ByteSize > maxBytes * 2 + 2 then
    throw "Simulation data exceeds the supported bound."
  parseHexBytes text

private def log (json : Json) : Except String Events.Log := do
  let address ← data (← field json "address") 20
  if address.size != 20 then throw "Invalid simulation log address."
  let topics ← (← field json "topics").getArr?
  if topics.size > 4 then throw "Invalid simulation log topic count."
  let topics ← topics.mapM fun value => do
    let topic ← data value 32
    if topic.size != 32 then throw "Invalid simulation log topic."
    return topic
  let bytes ← data (← field json "data") 65536
  return {
    address := address.data.foldl (fun n b => n * 256 + b.toNat) 0
    topics := topics
    data := bytes }

structure Passed where
  hash : ByteArray
  blockNumber : Nat
  gasUsed : Nat
  deriving Inhabited

/-- Reject incomplete, failed or contradictory simulation results. Successful
admission requires one exact EntryPoint success and every expected pool event.
These bytes remain a provider claim, not authenticated Ethereum evidence. -/
def parsePassed (chainId : Nat) (op : UserOperation)
    (expected : List Events.ExpectedWithdrawal) (json : Json) : Except String Passed := do
  if json.compress.toUTF8.size > 1024 * 1024 || expected.isEmpty || expected.length > 12 then
    throw "Simulation response exceeds the supported bound."
  let blocks ← json.getArr?
  if blocks.size != 1 then throw "Simulation did not return exactly one block."
  let block := blocks[0]!
  let number ← quantity (← field block "number")
  if number >= 2 ^ 64 then throw "Invalid simulation block number."
  let calls ← (← field block "calls").getArr?
  if calls.size != 1 then throw "Simulation did not return exactly one call."
  let call := calls[0]!
  if (← field call "status") != toJson ("0x1" : String) then
    throw "Full signed operation simulation failed."
  let used ← quantity (← field call "gasUsed")
  if used > gasLimit op then throw "Simulation gas use exceeds the request."
  let rawLogs ← (← field call "logs").getArr?
  if rawLogs.size > 4096 then throw "Simulation returned too many logs."
  let logs ← rawLogs.toList.mapM log
  let hash ← userOperationHash chainId Bundler.entryPoint op
  let some paymaster := op.paymaster | throw "Missing simulation paymaster."
  let entry : Events.ExpectedEntry := {
    entryPoint := Bundler.entryPoint, userOpHash := hash,
    sender := op.sender, paymaster, nonce := op.nonce }
  if Events.batchOutcome true logs entry expected != .confirmed then
    throw "Simulation lacks exact successful operation and pool event evidence."
  return { hash, blockNumber := number, gasUsed := used }

end Tornado.Protocol.EntryPointSimulation
