import Tornado.Runtime.HistorySnapshot
import Tornado.Runtime.HistorySync

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.HistoryReducer
open Tornado.Runtime.HistorySnapshotManifest

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def checked (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

private def rejects (action : IO α) (message : String) : IO Unit := do
  let failed ← try
      let _ ← action
      pure false
    catch _ => pure true
  require failed message

private def word (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do
    bytes := bytes.push ((value / 256 ^ (31 - i) % 256).toUInt8)
  return bytes

private def quantity (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def envelope (id : Nat) (value : Json) : String :=
  (Json.mkObj [("jsonrpc", toJson ("2.0" : String)),
    ("id", toJson id), ("result", value)]).compress

private def poolAddress : Nat := 0x199112eb461ea7eec1d75b33343542e1d069b41c
private def poolText : String := "0x199112eb461ea7eec1d75b33343542e1d069b41c"

private def mockTransport (state : State) (head : Nat) (checkpointChanged : Bool)
    (historyRequests : IO.Ref (Array Nat)) : IO HistorySync.Transport := do
  let fresh ← checked <| SelectedPoolBootstrap.freshState state.chainId state.pool
  let event := Json.mkObj [
    ("address", toJson poolText),
    ("blockNumber", toJson (quantity fresh.registeredBlock)),
    ("logIndex", toJson ("0x0" : String)), ("removed", toJson false),
    ("transactionIndex", toJson ("0x0" : String)),
    ("transactionHash", toJson ("0x" ++ bytesToHex (word 333))),
    ("blockHash", toJson ("0x" ++ bytesToHex (word 111))),
    ("topics", toJson #["0x" ++ bytesToHex (keccak256 "Deposit(bytes32,uint32,uint256)".toUTF8),
      "0x" ++ bytesToHex (word 1)]),
    ("data", toJson ("0x" ++ bytesToHex (word 0 ++ word 1)))]
  return {
    sagaIndex := throw <| IO.userError "Saga disabled in snapshot test",
    sagaChunk := fun _ => throw <| IO.userError "Saga disabled in snapshot test",
    nowMs := pure 0,
    rpc := fun id method params => do
      match method with
      | .chainId => return envelope id (toJson ("0x1" : String))
      | .blockNumber => return envelope id (toJson (quantity head))
      | .getBlockByNumber =>
        let number ← checked <| JsonRpc.parseHexQuantity (← checked params[0]!.getStr?)
        let hash := if checkpointChanged && number == state.lastSyncedBlock then word 222 else word 111
        return envelope id (Json.mkObj [
          ("number", toJson (quantity number)),
          ("hash", toJson ("0x" ++ bytesToHex hash))])
      | .call =>
        let data ← checked <| (← checked <| params[0]!.getObjVal? "data").getStr?
        if data == "0x" ++ bytesToHex (Abi.selector "nextIndex()") then
          return envelope id (toJson ("0x" ++ bytesToHex (word 1)))
        if data == "0x" ++ bytesToHex (Abi.selector "getLastRoot()") then
          return envelope id (toJson ("0x" ++ bytesToHex (word (state.verifiedRoot.getD 0))))
        throw <| IO.userError "Unexpected snapshot test call"
      | .getLogs =>
        let filter := params[0]!
        let first ← checked <| JsonRpc.parseHexQuantity
          (← checked <| (← checked <| filter.getObjVal? "fromBlock").getStr?)
        let last ← checked <| JsonRpc.parseHexQuantity
          (← checked <| (← checked <| filter.getObjVal? "toBlock").getStr?)
        historyRequests.modify (·.push first)
        return envelope id (Json.arr (if first <= fresh.registeredBlock &&
          fresh.registeredBlock <= last then #[event] else #[]))
      | _ => throw <| IO.userError "Unexpected snapshot test RPC" }

def main (args : List String) : IO UInt32 := do
  let [directory] := args
    | throw <| IO.userError "Usage: history_snapshot_test <existing-private-test-directory>"
  ProtectedIO.checkPrivateDirectory directory
  let some descriptor := descriptors.find? (fun row => row.chainId == 1 && row.pool == poolAddress)
    | throw <| IO.userError "Missing pinned fixture descriptor"
  let fixture ← IO.FS.readBinFile ("fixtures/history-snapshot/history/" ++ descriptor.file)
  let imported ← checked <| HistorySnapshot.decodePinned descriptor fixture
  require (imported.deposits.size == 20 && imported.withdrawals.size == 8 &&
    imported.deposits.all (fun row => !row.logIndexKnown))
    "Pinned SDK snapshot identity or unknown log-index handling changed"
  require (!(HistorySnapshot.decodePinned descriptor (fixture.set! 100 0xff)).isOk)
    "Modified pinned snapshot was accepted"
  require (!(HistorySnapshot.decodePinned { descriptor with sha256 := String.ofList (List.replicate 64 '0') } fixture).isOk)
    "Pinned snapshot with a wrong expected digest was accepted"
  require (!(HistorySnapshot.decodePinned
    { descriptor with jsonBytes := HistorySnapshot.maxPinnedBytes + 1 } fixture).isOk)
    "Pinned snapshot output bound was ignored"
  let loadedPinned ← HistorySnapshot.loadPinned "fixtures/history-snapshot" 1 poolAddress
  require (loadedPinned.isSome) "Pinned local assets directory was not loaded"
  let fresh ← checked <| SelectedPoolBootstrap.freshState 1 poolAddress
  let root ← checked <| buildMimcTree #[1]
  let record : DepositRecord := {
    commitment := word 1, leafIndex := 0, timestamp := 1,
    blockNumber := fresh.registeredBlock, logIndex := 0 }
  let state : State := { fresh with
    lastSyncedBlock := fresh.registeredBlock + 8000,
    verifiedRoot := some root.root, deposits := #[record] }
  HistorySnapshot.saveCache directory none state (word 111)
  let some saved ← HistorySnapshot.loadCache directory 1 poolAddress
    | throw <| IO.userError "Native snapshot did not roundtrip"
  require (saved.state.lastSyncedBlock == state.lastSyncedBlock &&
    saved.state.deposits.size == 1 && saved.blockHash == word 111)
    "Native snapshot changed public state"
  let calls ← IO.mkRef #[]
  let transport ← mockTransport state (state.lastSyncedBlock + 2) false calls
  let synchronized ← HistorySync.syncSelectedPoolWithAssets transport fresh none (some directory) false
  let firstCalls ← calls.get
  require (synchronized.state.deposits.size == 1 && !firstCalls.isEmpty &&
    firstCalls.all (· > fresh.registeredBlock))
    "Accepted native snapshot did not resume from bounded replay overlap"
  rejects (HistorySnapshot.saveCache directory (some saved)
    { state with lastSyncedBlock := state.lastSyncedBlock + 1 } (word 111))
    "Stale native cache writer overwrote a newer index"
  let some current ← HistorySnapshot.loadCache directory 1 poolAddress
    | throw <| IO.userError "Updated cache disappeared"
  require (current.state.lastSyncedBlock == synchronized.state.lastSyncedBlock)
    "Rejected stale cache writer changed the checkpoint"
  let calls ← IO.mkRef #[]
  let changed ← mockTransport current.state (current.state.lastSyncedBlock + 2) true calls
  let rebuilt ← HistorySync.syncSelectedPoolWithAssets changed fresh none (some directory) false
  require (rebuilt.state.deposits.size == 1 &&
    (← calls.get).any (· == fresh.registeredBlock))
    "Changed checkpoint hash did not discard and rebuild cached history"
  let latest ← HistorySnapshot.loadCache directory 1 poolAddress
  let some latest := latest | throw <| IO.userError "Rebuilt cache disappeared"
  let calls ← IO.mkRef #[]
  let head := latest.state.lastSyncedBlock + 2
  let base ← mockTransport latest.state head false calls
  let headReads ← IO.mkRef (0 : Nat)
  let changing : HistorySync.Transport := { base with rpc := fun id method params => do
    if method == .getBlockByNumber then
      let block ← checked <| JsonRpc.parseHexQuantity (← checked params[0]!.getStr?)
      if block == head then
        let prior ← headReads.get
        headReads.set (prior + 1)
        return envelope id (Json.mkObj [
          ("number", toJson (quantity head)),
          ("hash", toJson ("0x" ++ bytesToHex (word (if prior == 0 then 111 else 999))))])
    base.rpc id method params }
  rejects (HistorySync.syncSelectedPoolWithAssets changing fresh none (some directory) false)
    "A chain reorganization during synchronization was accepted"
  let some unchanged ← HistorySnapshot.loadCache directory 1 poolAddress
    | throw <| IO.userError "Failed synchronization removed the cache"
  require (unchanged.indexBytes == latest.indexBytes)
    "Failed synchronization published an updated cache"
  let entries ← (System.FilePath.mk directory).readDir
  let some chunk := entries.find? (fun entry => entry.fileName.startsWith "history-chunk-")
    | throw <| IO.userError "Missing content-addressed protected chunk"
  let bytes ← ProtectedIO.readPrivate chunk.path.toString
  ProtectedIO.replacePrivate chunk.path.toString bytes "[]".toUTF8
  rejects (HistorySnapshot.loadCache directory 1 poolAddress)
    "A corrupt content-addressed chunk was accepted"
  IO.println "PASS: pinned snapshot hashes, protected chunk cache, checkpoint revalidation, reorg rebuild, and stale CAS rejection"
  return 0
