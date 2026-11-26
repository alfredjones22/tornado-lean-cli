import Tornado.Runtime.HistorySync

namespace Tornado.Runtime.HistorySync.Test

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol
open Tornado.Protocol.HistoryReducer Tornado.Runtime.HistorySync

private def require (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw <| IO.userError s!"{label}: assertion failed"

private def checked (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def someOrFail (label : String) (value : Option α) : IO α :=
  match value with
  | some result => pure result
  | none => throw <| IO.userError label

private def expectFailure (label : String) (action : IO α) : IO Unit := do
  let failed ← try
      let _ ← action
      pure false
    catch _ => pure true
  require label failed

private def word (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do
    bytes := bytes.push (UInt8.ofNat ((value / 256 ^ (31 - i)) % 256))
  return bytes

private def wordHex (value : Nat) : String :=
  "0x" ++ bytesToHex (word value)

private def envelope (id : Nat) (value : Json) : String :=
  (Json.mkObj [("jsonrpc", toJson ("2.0" : String)),
    ("id", toJson id), ("result", value)]).compress

private def errorEnvelope (id : Nat) : String :=
  (Json.mkObj [("jsonrpc", toJson ("2.0" : String)),
    ("id", toJson id), ("error", Json.mkObj [
      ("code", toJson (-32602 : Int)),
      ("message", toJson ("Invalid parameters: block range limit" : String))])]).compress

private def fixtureResult (filename : String) : IO (Array Json) := do
  let raw ← IO.FS.readFile ("fixtures/saga-history/" ++ filename)
  let json ← checked filename (Json.parse raw)
  checked filename ((← checked filename (json.getObjVal? "result")).getArr?)

private def fixtureBytes (filename : String) : IO ByteArray :=
  IO.FS.readBinFile ("fixtures/saga-history/" ++ filename)

private def jsonQuantity (label : String) (json : Json) : IO Nat := do
  let raw ← checked label json.getStr?
  checked label (Tornado.Runtime.JsonRpc.parseHexQuantity raw)

structure MockConfig where
  index : String := "valid-index.json"
  chain : Nat := 1
  head : Nat := 108
  wrongRoot : Bool := false
  wrongCount : Bool := false
  wrongPool : Bool := false
  removedLog : Bool := false
  omitWithdrawal : Bool := false
  badChunk : Bool := false
  splitWidth : Nat := 0
  invalidSecondSlice : Bool := false
  flipChain : Bool := false
  alwaysRejectLogs : Bool := false
  expireDeadline : Bool := false
  deriving Inhabited

private def makeMock (config : MockConfig) (rootOne rootTwo : Nat) :
    IO (Transport × IO.Ref Nat) := do
  let logs ← fixtureResult (if config.wrongPool then
    "rpc-wrong-pool-logs.json" else if config.removedLog then
    "rpc-removed-logs.json" else "rpc-valid-logs.json")
  let logCalls ← IO.mkRef 0
  let chainCalls ← IO.mkRef 0
  let clockCalls ← IO.mkRef 0
  let transport : Transport := {
    sagaIndex := fixtureBytes config.index
    sagaChunk := fun segment =>
      if config.badChunk then pure "wrong chunk bytes".toUTF8
      else fixtureBytes segment.file
    rpc := fun id method params => do
      match method with
      | .chainId =>
        let previous ← chainCalls.get
        chainCalls.set (previous + 1)
        return envelope id (toJson (if config.chain == 1 &&
          !(config.flipChain && previous > 0) then "0x1" else "0xaa36a7"))
      | .blockNumber =>
        return envelope id (toJson ("0x" ++ String.ofList (Nat.toDigits 16 config.head)))
      | .call =>
        let call ← someOrFail "missing call" params[0]?
        let data ← checked "call data" ((← checked "call data" (call.getObjVal? "data")).getStr?)
        let block ← jsonQuantity "call block" (← someOrFail "missing block" params[1]?)
        let count := if block < 102 then 1 else 2
        let root := if block < 102 then rootOne else rootTwo
        if data == "0x" ++ bytesToHex (Abi.selector "nextIndex()") then
          return envelope id (toJson (wordHex (count + if config.wrongCount then 1 else 0)))
        if data == "0x" ++ bytesToHex (Abi.selector "getLastRoot()") then
          return envelope id (toJson (wordHex (root + if config.wrongRoot then 1 else 0)))
        throw <| IO.userError "Unexpected pool eth_call selector"
      | .getLogs =>
        logCalls.modify (· + 1)
        let filter ← someOrFail "missing filter" params[0]?
        let fromBlock ← jsonQuantity "fromBlock"
          (← checked "fromBlock" (filter.getObjVal? "fromBlock"))
        let toBlock ← jsonQuantity "toBlock"
          (← checked "toBlock" (filter.getObjVal? "toBlock"))
        if config.alwaysRejectLogs ||
            (config.splitWidth > 0 && toBlock - fromBlock + 1 > config.splitWidth) then
          return errorEnvelope id
        if config.invalidSecondSlice && fromBlock ≥ 105 then
          return "malformed RPC response"
        let mut selected := #[]
        for item in logs do
          let block ← jsonQuantity "fixture block" (← checked "fixture block" (item.getObjVal? "blockNumber"))
          if fromBlock ≤ block && block ≤ toBlock then
            if !config.omitWithdrawal || block != 106 then
              selected := selected.push item
        return envelope id (Json.arr selected)
      | _ => throw <| IO.userError "Unexpected RPC method"
    nowMs := do
      let old ← clockCalls.get
      clockCalls.set (old + 1)
      return if config.expireDeadline then old * (maxRunMs + 1) else 0
  }
  return (transport, logCalls)

private def existingState : IO State := do
  let fresh ← checked "fresh state" (emptyState 1 170 100)
  let first : DepositRecord := { commitment := word 1, leafIndex := 0, timestamp := 1, blockNumber := 100, logIndex := 0 }
  let prior : State := { fresh with lastSyncedBlock := 101, finalizedBlock := some 101, deposits := #[first] }
  let _ ← checked "existing state" (validateState prior)
  return prior

def main : IO Unit := do
  let prior ← existingState
  let commitment ← checked "fixture commitment" (parseHexBytes
    "0x1111111111111111111111111111111111111111111111111111111111111111")
  let value := commitment.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let one ← checked "one-leaf root" (buildMimcTree #[1])
  let two ← checked "two-leaf root" (buildMimcTree #[1, value])

  let (fullTransport, fullCalls) ← makeMock {} one.root two.root
  let full ← syncSelectedPool fullTransport prior
  require "complete Saga reaches captured head" (full.capturedHead == 108 &&
    full.sagaCoverage == some 108 && full.rpcSlices == 0 &&
    full.state.lastSyncedBlock == 108 && full.state.deposits.size == 2 &&
    full.state.withdrawals.size == 1 && (← fullCalls.get) == 0)

  let (shortTransport, shortCalls) ← makeMock { index := "short-index.json" } one.root two.root
  let short ← syncSelectedPool shortTransport prior
  require "partial Saga requires RPC tail" (short.sagaCoverage == some 104 &&
    short.state.lastSyncedBlock == 108 && short.state.withdrawals.size == 1 &&
    short.rpcSlices == 1 && (← shortCalls.get) == 1)

  let (badIndex, fallbackCalls) ← makeMock { index := "gap-index.json" } one.root two.root
  let fallback ← syncSelectedPool badIndex prior
  require "invalid index falls back to original cursor" (fallback.sagaCoverage == none &&
    fallback.state.lastSyncedBlock == 108 && fallback.state.deposits.size == 2 &&
    fallback.state.withdrawals.size == 1 && (← fallbackCalls.get) == 1)

  let (badChunk, chunkCalls) ← makeMock { badChunk := true } one.root two.root
  let afterChunk ← syncSelectedPool badChunk prior
  require "invalid chunk falls back to RPC" (afterChunk.sagaCoverage == none &&
    afterChunk.state.lastSyncedBlock == 108 && (← chunkCalls.get) == 1)

  let (splitTransport, splitCalls) ← makeMock { index := "gap-index.json", splitWidth := 3 }
    one.root two.root
  let split ← syncSelectedPool splitTransport prior
  require "RPC range rejection bisects and rejoins" (split.state.lastSyncedBlock == 108 &&
    split.rpcSlices > 1 && (← splitCalls.get) > split.rpcSlices)

  let (wrongChain, _) ← makeMock { chain := 11155111 } one.root two.root
  expectFailure "wrong chain" (syncSelectedPool wrongChain prior)
  let (changedChain, _) ← makeMock { flipChain := true } one.root two.root
  expectFailure "chain changes during scan" (syncSelectedPool changedChain prior false)
  let (wrongPool, _) ← makeMock { wrongPool := true } one.root two.root
  expectFailure "wrong pool log" (syncSelectedPool wrongPool prior false)
  let (removedLog, _) ← makeMock { removedLog := true } one.root two.root
  expectFailure "removed log" (syncSelectedPool removedLog prior false)
  let (wrongRoot, _) ← makeMock { wrongRoot := true } one.root two.root
  expectFailure "wrong same-block root" (syncSelectedPool wrongRoot prior)
  let (wrongCount, _) ← makeMock { wrongCount := true } one.root two.root
  expectFailure "wrong same-block count" (syncSelectedPool wrongCount prior)
  let invalidTail : MockConfig := { index := "gap-index.json", splitWidth := 4, invalidSecondSlice := true }
  let (badSecond, _) ← makeMock invalidTail one.root two.root
  expectFailure "failed second slice has no returned state" (syncSelectedPool badSecond prior)
  require "failed slice leaves caller state immutable" (prior.lastSyncedBlock == 101)
  let (alwaysReject, _) ← makeMock { alwaysRejectLogs := true } one.root two.root
  expectFailure "bounded split eventually rejects" (syncSelectedPool alwaysReject prior false)
  let (oversizedWindow, oversizedCalls) ← makeMock { head := 2100200 } one.root two.root
  let windowMessage ← try
      let _ ← syncSelectedPool oversizedWindow prior false
      pure ""
    catch error => pure error.toString
  require "RPC scan window cap and archive guidance"
    (windowMessage == "Pool history exceeds the bounded RPC replay window. Use --rpc with an archive endpoint that can validate the bundled checkpoint.")
  require "overlarge window fails before log reads" ((← oversizedCalls.get) == 0)
  let (deadline, _) ← makeMock { expireDeadline := true } one.root two.root
  expectFailure "aggregate deadline" (syncSelectedPool deadline prior)
  require "aggregate bytes exact limit" (withinAggregateBytes maxAggregateBytes 0)
  require "aggregate bytes overflow rejected" (!withinAggregateBytes maxAggregateBytes 1)
  let firstSlice : RpcHistory.CheckedSlice := { fromBlock := 101, toBlock := 104, events := #[] }
  let skippedSlice : RpcHistory.CheckedSlice := { fromBlock := 106, toBlock := 108, events := #[] }
  require "combiner rejects slice gap" (match combineSlices 101 108 #[firstSlice, skippedSlice] with
    | .error _ => true | .ok _ => false)

  let (omitted, _) ← makeMock { omitWithdrawal := true } one.root two.root
  let falseComplete ← syncSelectedPool omitted prior false
  require "provider omission remains a documented limitation"
    (falseComplete.state.lastSyncedBlock == 108 &&
      falseComplete.state.deposits.size == 2 &&
      falseComplete.state.withdrawals.isEmpty)
  IO.println "PASS: bounded live-history orchestration, Saga/RPC fallback, split, same-block claims, and fault gates"

end Tornado.Runtime.HistorySync.Test

def main : IO Unit := Tornado.Runtime.HistorySync.Test.main
