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

private def failureMessage (action : IO α) : IO String := do
  try
    let _ ← action
    return ""
  catch error => return error.toString

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

private def unavailableEnvelope (id : Nat) : String :=
  (Json.mkObj [("jsonrpc", toJson ("2.0" : String)),
    ("id", toJson id), ("error", Json.mkObj [
      ("code", toJson (-32000 : Int)),
      ("message", toJson ("historical state UNTRUSTED_PROVIDER_DETAIL is not available" : String))])]).compress

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

private structure CatchUpConfig where
  oldReorg : Bool := false
  newReorg : Bool := false
  expire : Bool := false
  overWindow : Bool := false
  badRoot : Bool := false
  badCount : Bool := false
  deriving Inhabited

private def advancingHeadCase (config : CatchUpConfig := {}) (cacheDir : Option String := none) :
    IO (Option HistorySync.Result × String × Array (Nat × Nat) × Nat) := do
  let fresh ← checked <| SelectedPoolBootstrap.freshState 1 poolAddress
  let firstRoot ← checked <| buildMimcTree #[1]
  let secondRoot ← checked <| buildMimcTree #[1, 2]
  let oldHead := fresh.registeredBlock + 1
  let newHead := oldHead + if config.overWindow then HistorySync.maxRpcScanBlocks + 1 else 1
  let heads ← IO.mkRef (0 : Nat)
  let oldHashes ← IO.mkRef (0 : Nat)
  let newHashes ← IO.mkRef (0 : Nat)
  let clock ← IO.mkRef (0 : Nat)
  let requests ← IO.mkRef (0 : Nat)
  let ranges ← IO.mkRef (#[] : Array (Nat × Nat))
  let event (commitment index block hash : Nat) := Json.mkObj [
    ("address", toJson poolText), ("blockNumber", toJson (quantity block)),
    ("logIndex", toJson ("0x0" : String)), ("removed", toJson false),
    ("transactionIndex", toJson ("0x0" : String)),
    ("transactionHash", toJson ("0x" ++ bytesToHex (word (333 + index)))),
    ("blockHash", toJson ("0x" ++ bytesToHex (word hash))),
    ("topics", toJson #["0x" ++ bytesToHex Events.depositTopic,
      "0x" ++ bytesToHex (word commitment)]),
    ("data", toJson ("0x" ++ bytesToHex (word index ++ word 1)))]
  let transport : HistorySync.Transport := {
    sagaIndex := throw <| IO.userError "No Saga in advancing-head test"
    sagaChunk := fun _ => throw <| IO.userError "No Saga in advancing-head test"
    nowMs := clock.get
    rpc := fun id method params => do
      let requested ← requests.get
      requests.set (requested + 1)
      require (id == requested + 1) "Catch-up reset the original request budget."
      match method with
      | .chainId => return envelope id (toJson ("0x1" : String))
      | .blockNumber =>
        let read ← heads.get
        heads.set (read + 1)
        if config.expire && read > 0 then clock.set (HistorySync.maxRunMs + 1)
        -- A third capture would advance again. The production run must stop
        -- after the second capture rather than following an unbounded head.
        return envelope id (toJson (quantity (if read == 0 then oldHead
          else if config.overWindow then newHead else oldHead + read)))
      | .getBlockByNumber =>
        let block ← checked <| JsonRpc.parseHexQuantity (← checked params[0]!.getStr?)
        let hash ← if block == oldHead then do
            let read ← oldHashes.get
            oldHashes.set (read + 1)
            pure (if config.oldReorg && read >= 2 then 999 else 111)
          else do
            let read ← newHashes.get
            newHashes.set (read + 1)
            pure (if config.newReorg && read > 0 then 999 else 222)
        return envelope id (Json.mkObj [("number", toJson (quantity block)),
          ("hash", toJson ("0x" ++ bytesToHex (word hash)))])
      | .getLogs =>
        if config.expire then clock.set (HistorySync.maxRunMs - 1)
        let filter := params[0]!
        let first ← checked <| JsonRpc.parseHexQuantity
          (← checked <| (← checked <| filter.getObjVal? "fromBlock").getStr?)
        let last ← checked <| JsonRpc.parseHexQuantity
          (← checked <| (← checked <| filter.getObjVal? "toBlock").getStr?)
        ranges.modify (·.push (first, last))
        let mut logs := #[]
        if first <= fresh.registeredBlock && fresh.registeredBlock <= last then
          logs := logs.push (event 1 0 fresh.registeredBlock 111)
        if first <= newHead && newHead <= last then
          logs := logs.push (event 2 1 newHead 222)
        return envelope id (Json.arr logs)
      | .call =>
        let block ← checked <| JsonRpc.parseHexQuantity (← checked params[1]!.getStr?)
        let data ← checked <| (← checked <| params[0]!.getObjVal? "data").getStr?
        let count := if block <= oldHead then 1 else 2 + if config.badCount then 1 else 0
        let root := if block <= oldHead then firstRoot.root
          else secondRoot.root + if config.badRoot then 1 else 0
        if data == "0x" ++ bytesToHex (Abi.selector "nextIndex()") then
          return envelope id (toJson ("0x" ++ bytesToHex (word count)))
        if data == "0x" ++ bytesToHex (Abi.selector "getLastRoot()") then
          return envelope id (toJson ("0x" ++ bytesToHex (word root)))
        throw <| IO.userError "Unexpected advancing-head pool call"
      | _ => throw <| IO.userError "Unexpected advancing-head RPC" }
  try
    let result ← HistorySync.syncSelectedPoolWithAssets transport fresh none cacheDir false
    return (some result, "", ← ranges.get, ← heads.get)
  catch error => return (none, error.toString, ← ranges.get, ← heads.get)

private def catchUpTests (directory : String) : IO Unit := do
  let fresh ← checked <| SelectedPoolBootstrap.freshState 1 poolAddress
  let oldHead := fresh.registeredBlock + 1
  let cacheDir := System.FilePath.mk directory / "catch-up-cache"
  IO.FS.createDir cacheDir
  IO.setAccessRights cacheDir { user := { read := true, write := true, execution := true } }
  let cache := some cacheDir.toString
  let (accepted, error, ranges, heads) ← advancingHeadCase {} cache
  let some accepted := accepted
    | throw <| IO.userError ("Expected caught-up history: " ++ error)
  require (error.isEmpty && accepted.capturedHead == oldHead + 1 &&
    accepted.state.lastSyncedBlock == oldHead + 1 && accepted.state.deposits.size == 2 &&
    accepted.state.finalizedBlock.isNone && accepted.rpcSlices == 2 && heads == 2 &&
    ranges == #[(fresh.registeredBlock, oldHead), (oldHead + 1, oldHead + 1)])
    "Advancing history failed to append exactly one captured tail or fabricated finality"
  let some saved ← HistorySnapshot.loadCache cacheDir.toString 1 poolAddress
    | throw <| IO.userError "Caught-up history was not saved"
  require (saved.state.lastSyncedBlock == oldHead + 1 && saved.state.deposits.size == 2 &&
    saved.blockHash == word 222 && saved.state.finalizedBlock.isNone)
    "Catch-up cache saved the initial cursor/hash instead of the final complete state"
  for config in ([{ oldReorg := true }, { newReorg := true },
      { badRoot := true }, { badCount := true }] : List CatchUpConfig) do
    let (accepted, _, _, heads) ← advancingHeadCase config cache
    require (accepted.isNone && heads == 2)
      "Catch-up accepted a changed old/new head, root or count"
  let (expired, message, ranges, heads) ← advancingHeadCase { expire := true } cache
  require (expired.isNone && message.contains "aggregate deadline exceeded" &&
    ranges.size == 1 && heads == 2)
    "Catch-up reset the initial sync's deadline or scanned after it expired"
  let (overWindow, message, ranges, heads) ← advancingHeadCase { overWindow := true } cache
  require (overWindow.isNone && message.contains "bounded RPC replay window" &&
    ranges.size == 1 && heads == 2)
    "Catch-up relaxed the bounded replay window or restarted full history"
  let some unchanged ← HistorySnapshot.loadCache cacheDir.toString 1 poolAddress
    | throw <| IO.userError "Failed catch-up removed the previously complete cache"
  require (unchanged.indexBytes == saved.indexBytes)
    "A failed catch-up published partial or changed cache evidence"

def main (args : List String) : IO UInt32 := do
  let [directory] := args
    | throw <| IO.userError "Usage: history_snapshot_test <existing-private-test-directory>"
  ProtectedIO.checkPrivateDirectory directory
  catchUpTests directory
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
  let some checkpoint ← HistorySnapshot.loadCache directory 1 poolAddress
    | throw <| IO.userError "Rebuilt cache disappeared"
  let calls ← IO.mkRef #[]
  let notices ← IO.mkRef (#[] : Array String)
  let base ← mockTransport checkpoint.state (checkpoint.state.lastSyncedBlock + 2) false calls
  let unavailable : HistorySync.Transport := { base with
    progress := fun message => notices.modify (·.push message)
    rpc := fun id method params => do
      if method == .call then
        let block ← checked <| JsonRpc.parseHexQuantity (← checked params[1]!.getStr?)
        if block == checkpoint.state.lastSyncedBlock then return unavailableEnvelope id
      base.rpc id method params }
  let rebuiltUnavailable ← HistorySync.syncSelectedPoolWithAssets unavailable fresh none (some directory) false
  require (rebuiltUnavailable.state.deposits.size == 1 &&
    (← calls.get).any (· == fresh.registeredBlock) &&
    (← notices.get).size == 1 &&
    (← notices.get).all (fun message => !message.contains "UNTRUSTED_PROVIDER_DETAIL"))
    "Unavailable cached checkpoint did not rebuild with a fixed public notice"
  let some checkpoint ← HistorySnapshot.loadCache directory 1 poolAddress
    | throw <| IO.userError "Rebuilt unavailable cache disappeared"
  let calls ← IO.mkRef #[]
  let base ← mockTransport checkpoint.state (checkpoint.state.lastSyncedBlock + 2) false calls
  let unavailableHash : HistorySync.Transport := { base with rpc := fun id method params => do
    if method == .getBlockByNumber then
      let block ← checked <| JsonRpc.parseHexQuantity (← checked params[0]!.getStr?)
      if block == checkpoint.state.lastSyncedBlock then return unavailableEnvelope id
    base.rpc id method params }
  let rebuiltHash ← HistorySync.syncSelectedPoolWithAssets unavailableHash fresh none (some directory) false
  require (rebuiltHash.state.deposits.size == 1 &&
    (← calls.get).any (· == fresh.registeredBlock))
    "Unavailable cached block hash did not rebuild the complete history"
  let calls ← IO.mkRef #[]
  let notices ← IO.mkRef (#[] : Array String)
  let base ← mockTransport state (imported.lastSyncedBlock + 2) false calls
  let prunedPinned : HistorySync.Transport := { base with
    progress := fun message => notices.modify (·.push message)
    rpc := fun id method params => do
      if method == .call then
        let block ← checked <| JsonRpc.parseHexQuantity (← checked params[1]!.getStr?)
        if block == imported.lastSyncedBlock then return unavailableEnvelope id
      base.rpc id method params }
  let rebuiltPinned ← HistorySync.syncSelectedPoolWithAssets prunedPinned fresh
    (some "fixtures/history-snapshot") none false
  require (rebuiltPinned.state.deposits.size == 1 &&
    rebuiltPinned.state.lastSyncedBlock == imported.lastSyncedBlock + 2 &&
    (← calls.get).any (· == fresh.registeredBlock) && (← notices.get).size == 1)
    "Pruned RPC state caused the authenticated pinned history to be accepted or prevented a complete rebuild"
  let tamperedRoot := System.FilePath.mk directory / "tampered-assets"
  let tamperedPath := tamperedRoot / "history" / descriptor.file
  IO.FS.createDirAll tamperedPath.parent.get!
  IO.FS.writeBinFile tamperedPath (fixture.set! 100 0xff)
  calls.set #[]
  notices.set #[]
  rejects (HistorySync.syncSelectedPoolWithAssets prunedPinned fresh
    (some tamperedRoot.toString) none false)
    "A tampered pinned snapshot was hidden by unavailable-checkpoint fallback"
  require ((← calls.get).isEmpty && (← notices.get).isEmpty)
    "Tampered pinned assets triggered fallback rather than failing closed"
  let some checkpoint ← HistorySnapshot.loadCache directory 1 poolAddress
    | throw <| IO.userError "Cache disappeared before malformed-checkpoint tests"
  let calls ← IO.mkRef #[]
  let base ← mockTransport checkpoint.state (checkpoint.state.lastSyncedBlock + 2) false calls
  let malformed : HistorySync.Transport := { base with rpc := fun id method params => do
    if method == .call then
      let block ← checked <| JsonRpc.parseHexQuantity (← checked params[1]!.getStr?)
      if block == checkpoint.state.lastSyncedBlock then return "UNTRUSTED_PROVIDER_DETAIL"
    base.rpc id method params }
  let malformedMessage ← failureMessage
    (HistorySync.syncSelectedPoolWithAssets malformed fresh none (some directory) false)
  require (malformedMessage.contains "checkpoint RPC returned a malformed response" &&
    !malformedMessage.contains "UNTRUSTED_PROVIDER_DETAIL" && (← calls.get).isEmpty)
    "Malformed checkpoint replies were reflected or silently rebuilt"
  let chainReads ← IO.mkRef (0 : Nat)
  let wrongChain : HistorySync.Transport := { base with rpc := fun id method params => do
    if method == .chainId then
      let reads ← chainReads.get
      chainReads.set (reads + 1)
      if reads > 0 then return envelope id (toJson ("0xaa36a7" : String))
    base.rpc id method params }
  rejects (HistorySync.syncSelectedPoolWithAssets wrongChain fresh none (some directory) false)
    "A checkpoint RPC chain change was hidden by unavailable-state fallback"
  require ((← calls.get).isEmpty) "A changed checkpoint chain triggered a history rebuild"
  let calls ← IO.mkRef #[]
  let base ← mockTransport checkpoint.state (checkpoint.state.lastSyncedBlock + 2) false calls
  let unavailableHead : HistorySync.Transport := { base with rpc := fun id method params => do
    if method == .call then
      let block ← checked <| JsonRpc.parseHexQuantity (← checked params[1]!.getStr?)
      if block == checkpoint.state.lastSyncedBlock + 2 then return unavailableEnvelope id
    base.rpc id method params }
  let unavailableMessage ← failureMessage
    (HistorySync.syncSelectedPoolWithAssets unavailableHead fresh none (some directory) false)
  require (unavailableMessage.contains "Try another RPC with historical state support" &&
    !unavailableMessage.contains "UNTRUSTED_PROVIDER_DETAIL")
    "A failed required head check was bypassed or reflected the provider's error message"
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
  rejects (HistorySync.syncSelectedPoolWithAssets unavailable fresh none (some directory) false)
    "A corrupt cache was hidden by unavailable-checkpoint fallback"
  IO.println "PASS: pinned snapshot hashes, protected chunk cache, checkpoint revalidation, reorg rebuild, and stale CAS rejection"
  return 0
