import Tornado.Protocol.HistoryReducer
import Tornado.Protocol.Abi
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.HistorySnapshot

/-!
Bounded, read-only pool-history orchestration. The live adapter uses the
bounded HTTPS GET/POST binding; tests inject a deterministic transport. An
accepted result has a cursor through the captured RPC head, but RPC truth,
Saga-index trust, deployed pool identity, and finality remain assumptions.
The optional assets/cache adapter persists only public selected-pool state.
This module never imports a private note or submits a transaction.
-/

namespace Tornado.Runtime.HistorySync

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol
open Tornado.Protocol.SagaHistory Tornado.Protocol.RpcHistory
open Tornado.Protocol.HistoryReducer Tornado.Runtime

def maxRunMs : Nat := 5 * 60 * 1000
def maxRpcRequests : Nat := 4096
def maxAggregateBytes : Nat := 256 * 1024 * 1024
def maxCombinedEvents : Nat := 1000000
def maxRpcScanBlocks : Nat := 2000000
def maxSplitDepth : Nat := 10

def withinAggregateBytes (previous amount : Nat) : Bool :=
  previous + amount ≤ maxAggregateBytes

theorem withinAggregateBytes_sound (previous amount : Nat)
    (h : withinAggregateBytes previous amount = true) :
    previous + amount ≤ maxAggregateBytes := by
  simpa [withinAggregateBytes] using h

structure Transport where
  sagaIndex : IO ByteArray
  sagaChunk : Segment → IO ByteArray
  rpc : Nat → JsonRpc.Method → Array Json → IO String
  nowMs : IO Nat

structure Budget where
  transport : Transport
  startedMs : Nat
  requests : IO.Ref Nat
  bytes : IO.Ref Nat
  decodedBytes : IO.Ref Nat

structure Result where
  state : State
  capturedHead : Nat
  sagaCoverage : Option Nat
  rpcSlices : Nat

private def fail (message : String) : IO α :=
  throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => fail message

private def newBudget (transport : Transport) : IO Budget := do
  return { transport, startedMs := ← transport.nowMs,
           requests := ← IO.mkRef 0, bytes := ← IO.mkRef 0,
           decodedBytes := ← IO.mkRef 0 }

private def checkDeadline (budget : Budget) : IO Unit := do
  if (← budget.transport.nowMs) > budget.startedMs + maxRunMs then
    fail "Pool-history aggregate deadline exceeded."

private def addBytes (budget : Budget) (amount : Nat) : IO Unit := do
  let previous ← budget.bytes.get
  if !withinAggregateBytes previous amount then
    fail "Pool-history aggregate byte budget exceeded."
  budget.bytes.set (previous + amount)

private def addDecodedBytes (budget : Budget) (amount : Nat) : IO Unit := do
  let previous ← budget.decodedBytes.get
  if !withinAggregateBytes previous amount then
    fail "Pool-history aggregate decoded Saga byte budget exceeded."
  budget.decodedBytes.set (previous + amount)

private def nextRequestId (budget : Budget) : IO Nat := do
  checkDeadline budget
  let previous ← budget.requests.get
  if previous ≥ maxRpcRequests then fail "Pool-history RPC request budget exceeded."
  budget.requests.set (previous + 1)
  return previous + 1

/-- An optional RPC transport result is only used for adaptive `eth_getLogs`
    splitting. Bounds and deadlines still throw and cannot be split away. -/
private def optionalRpc (budget : Budget) (method : JsonRpc.Method)
    (params : Array Json) : IO (Option (Nat × String)) := do
  let id ← nextRequestId budget
  let raw? ← try
      some <$> budget.transport.rpc id method params
    catch _ => pure none
  checkDeadline budget
  let some raw := raw? | return none
  if raw.toUTF8.size > RpcHistory.maxRpcResponseBytes then
    fail "Pool-history RPC response exceeds one MiB."
  addBytes budget raw.toUTF8.size
  return some (id, raw)

private def requiredRpc (budget : Budget) (method : JsonRpc.Method)
    (params : Array Json) : IO (Nat × String) := do
  let some response ← optionalRpc budget method params
    | fail "Pool-history RPC request failed."
  return response

private def quantityHex (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def addressHex (address : Nat) : String := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:20] do
    bytes := bytes.push (UInt8.ofNat ((address / 256 ^ (19 - i)) % 256))
  return "0x" ++ bytesToHex bytes

private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def abiWord (json : Json) : Except String Nat := do
  let raw ← json.getStr?
  if !raw.startsWith "0x" then throw "Pool eth_call result has no 0x prefix."
  let bytes ← parseHexBytes raw
  if bytes.size != 32 then throw "Pool eth_call result is not one ABI word."
  return wordNat bytes

private def poolCallParams (pool : Nat) (signature : String) (block : Nat) :
    Array Json :=
  #[Json.mkObj [("to", toJson (addressHex pool)),
    ("data", toJson ("0x" ++ bytesToHex (Abi.selector signature)))],
    toJson (quantityHex block)]

/-- Exact-block root and leaf-count claims from the *same configured RPC*.
    The block number labels requests but does not authenticate the provider. -/
private def poolClaims (budget : Budget) (selection : Selection) (block : Nat) :
    IO (Nat × Nat) := do
  let (chainId, chainRaw) ← requiredRpc budget .chainId #[]
  let chain ← checked <| JsonRpc.parseQuantityResult chainId chainRaw
  if chain != selection.chainId then fail "Pool-history RPC chain changed."
  let (countId, countRaw) ← requiredRpc budget .call
    (poolCallParams selection.pool "nextIndex()" block)
  let count ← checked <| abiWord (← checked <| JsonRpc.parseResult countId countRaw)
  if count ≥ 2 ^ 32 then fail "Pool nextIndex is not uint32."
  let (rootId, rootRaw) ← requiredRpc budget .call
    (poolCallParams selection.pool "getLastRoot()" block)
  let root ← checked <| abiWord (← checked <| JsonRpc.parseResult rootId rootRaw)
  return (count, root)

private def captureSelection (budget : Budget) (prior : State) : IO Selection := do
  let _ ← checked (validateState prior)
  let (chainId, chainRaw) ← requiredRpc budget .chainId #[]
  let chain ← checked <| JsonRpc.parseQuantityResult chainId chainRaw
  if chain != prior.chainId then fail "Selected pool RPC is on another chain."
  let (headId, headRaw) ← requiredRpc budget .blockNumber #[]
  let head ← checked <| JsonRpc.parseQuantityResult headId headRaw
  if head < prior.lastSyncedBlock || head < prior.registeredBlock then
    fail "Pool-history RPC head precedes the saved pool cursor or registration."
  return { chainId := prior.chainId, pool := prior.pool,
           registeredBlock := prior.registeredBlock,
           lastSyncedBlock := prior.lastSyncedBlock,
           finalizedBlock := prior.finalizedBlock, head := head }

private def getSaga (budget : Budget) (prior : State) (selection : Selection) :
    IO (State × Nat) := do
  checkDeadline budget
  let index ← budget.transport.sagaIndex
  checkDeadline budget
  if index.size > SagaHistory.maxIndexBytes then
    fail "Saga index exceeds two MiB."
  addBytes budget index.size
  let plan ← checked (SagaHistory.planIndex selection index)
  let mut chunks : Array ByteArray := #[]
  let mut total := 0
  for segment in plan.segments do
    checkDeadline budget
    let bytes ← budget.transport.sagaChunk segment
    checkDeadline budget
    if bytes.size > SagaHistory.maxCompressedChunkBytes then
      fail "Saga chunk exceeds 32 MiB."
    total := total + bytes.size
    if total > SagaHistory.maxAggregateCompressedBytes then
      fail "Saga selected chunks exceed aggregate byte budget."
    addBytes budget bytes.size
    -- Decode once here so the run-level bound applies to expanded content.
    -- The pure Saga validator accepts raw JSONL and still checks its digest,
    -- event shape, ordering, and selected-pool coverage.
    let decoded ← if bytes[0]? == some 0x1f && bytes[1]? == some 0x8b then
        checked (Tornado.Compression.Gzip.decompress bytes
          SagaHistory.maxDecodedChunkBytes)
      else pure bytes
    if decoded.size > SagaHistory.maxDecodedChunkBytes then
      fail "Saga decoded chunk exceeds 32 MiB."
    addDecodedBytes budget decoded.size
    chunks := chunks.push decoded
  let history ← checked (SagaHistory.validateChunks plan chunks)
  let (count, root) ← poolClaims budget selection history.coverage
  let finalized := prior.finalizedBlock.getD 0
  let state ← checked (HistoryReducer.applySaga prior selection history
    finalized history.coverage count root)
  checkDeadline budget
  return (state, history.coverage)

private def rangeRejection (message : String) : Bool :=
  let lower := message.toLower
  lower.startsWith "json-rpc " &&
    (lower.contains "range" || lower.contains "limit" ||
      lower.contains "too many" || lower.contains "invalid parameters")

/-- A failed *request* may be bisected. A successfully returned but malformed
    or wrong-chain response never gets split into apparent success. -/
private def fetchRange (budget : Budget) (selection : Selection)
    (fromBlock toBlock fuel : Nat) : IO (Array CheckedSlice) := do
  let params ← checked (RpcHistory.requestParams selection fromBlock toBlock)
  let (chainId, chainRaw) ← requiredRpc budget .chainId #[]
  let chain ← checked <| JsonRpc.parseQuantityResult chainId chainRaw
  if chain != selection.chainId then fail "Pool-history RPC chain changed."
  let logs? ← optionalRpc budget .getLogs params
  let slice? ← match logs? with
    | none => pure none
    | some (logsId, logsRaw) =>
      match JsonRpc.parseResult logsId logsRaw with
      | .error message =>
        if rangeRejection message then pure none
        else fail "Pool-history RPC rejected log request."
      | .ok _ =>
        let slice ← checked <| RpcHistory.parseRange selection fromBlock toBlock
          chainId logsId chainRaw logsRaw
        pure (some slice)
  if let some slice := slice? then return #[slice]
  if fromBlock ≥ toBlock then
    fail "Pool-history RPC log range failed after bounded splitting."
  match fuel with
  | 0 => fail "Pool-history RPC log range failed after bounded splitting."
  | fuel' + 1 =>
    let middle := fromBlock + (toBlock - fromBlock) / 2
    let left ← fetchRange budget selection fromBlock middle fuel'
    let right ← fetchRange budget selection (middle + 1) toBlock fuel'
    return left ++ right
termination_by fuel

/-- Concatenation is admitted only for exact adjacent, head-reaching slices. -/
def combineSlices (fromBlock head : Nat) (slices : Array CheckedSlice) :
    Except String CheckedSlice := do
  if fromBlock > head then throw "Pool-history RPC range is inverted."
  let mut cursor := fromBlock
  let mut events := #[]
  for slice in slices do
    if slice.fromBlock != cursor || slice.toBlock < cursor || slice.toBlock > head then
      throw "Pool-history RPC slices have a gap, overlap, or excess block."
    if events.size + slice.events.size > maxCombinedEvents then
      throw "Pool-history RPC event budget exceeded."
    events := events ++ slice.events
    cursor := slice.toBlock + 1
  if cursor != head + 1 then throw "Pool-history RPC slices stop before the head."
  return { fromBlock, toBlock := head, events }

private def scanRpc (budget : Budget) (selection : Selection)
    (fromBlock : Nat) : IO (CheckedSlice × Nat) := do
  if fromBlock > selection.head ||
      selection.head - fromBlock + 1 > maxRpcScanBlocks then
    fail "Pool-history RPC scan is empty or exceeds the bounded block window."
  let mut cursor := fromBlock
  let mut slices : Array CheckedSlice := #[]
  while cursor ≤ selection.head do
    checkDeadline budget
    let last := min selection.head (cursor + RpcHistory.maxRpcBlocks - 1)
    let fetched ← fetchRange budget selection cursor last maxSplitDepth
    slices := slices ++ fetched
    cursor := last + 1
  let combined ← checked (combineSlices fromBlock selection.head slices)
  return (combined, slices.size)

/-- The only success exit of the orchestrator requires the selected pool's
    saved cursor to reach the captured head. It does not prove RPC completeness. -/
def acceptComplete (selection : Selection) (state : State) : Except String State :=
  match SagaHistory.assertPoolFreshness selection
      { chainId := state.chainId, pool := state.pool,
        lastSyncedBlock := state.lastSyncedBlock } with
  | .ok _ => .ok state
  | .error message => .error message

theorem acceptComplete_success_fresh (selection : Selection) (state result : State)
    (h : acceptComplete selection state = .ok result) :
    result.chainId = selection.chainId ∧ result.pool = selection.pool ∧
      selection.head ≤ result.lastSyncedBlock := by
  unfold acceptComplete at h
  cases hf : SagaHistory.assertPoolFreshness selection
      { chainId := state.chainId, pool := state.pool,
        lastSyncedBlock := state.lastSyncedBlock } with
  | error _ => simp [hf] at h
  | ok _ =>
      simp [hf] at h
      cases h
      exact SagaHistory.accepted_freshness_covers_head selection
        { chainId := state.chainId, pool := state.pool,
          lastSyncedBlock := state.lastSyncedBlock } hf

/-- No result is returned for a partial scan. On Saga failure, RPC starts
    from the original trusted state; a partially parsed Saga is never kept. -/
private def syncWithBudget (budget : Budget) (prior : State)
    (useSaga : Bool) (captured : Option Selection := none) : IO Result := do
  let selection ← match captured with
    | none => captureSelection budget prior
    | some selected => pure selected
  let saga? ← if useSaga then
      try some <$> getSaga budget prior selection
      catch _ => pure none
    else pure none
  let baseState := saga?.map (·.1) |>.getD prior
  let coverage := saga?.map (·.2)
  let fromBlock := match coverage with
    | some block => block + 1
    | none => SagaHistory.firstReplayBlock selection
  let mut state := baseState
  let mut rpcSlices := 0
  if fromBlock ≤ selection.head then
    let (slice, count) ← scanRpc budget selection fromBlock
    let (leafCount, root) ← poolClaims budget selection selection.head
    let rpcSelection := { selection with
      lastSyncedBlock := state.lastSyncedBlock,
      finalizedBlock := state.finalizedBlock }
    state ← checked (HistoryReducer.applyRpc state rpcSelection slice
      (prior.finalizedBlock.getD 0) selection.head leafCount root)
    rpcSlices := count
  state ← checked (acceptComplete selection state)
  checkDeadline budget
  return { state, capturedHead := selection.head, sagaCoverage := coverage,
           rpcSlices }

def syncSelectedPool (transport : Transport) (prior : State)
    (useSaga : Bool := true) : IO Result := do
  syncWithBudget (← newBudget transport) prior useSaga

private def blockHash (budget : Budget) (number : Nat) : IO ByteArray := do
  let (id, raw) ← requiredRpc budget .getBlockByNumber
    #[toJson (quantityHex number), toJson false]
  let json ← checked <| JsonRpc.parseResult id raw
  if json == .null then fail "Pool-history checkpoint block is unavailable."
  let reported ← checked <| JsonRpc.parseHexQuantity
    (← checked <| (← checked <| json.getObjVal? "number").getStr?)
  let hash ← checked <| parseHexBytes
    (← checked <| (← checked <| json.getObjVal? "hash").getStr?)
  if reported != number || hash.size != 32 then
    fail "Pool-history checkpoint block is malformed."
  return hash

/-- A cache is never admitted on its own cursor claim: recompute its deposit
    root, compare count/root at that exact block, and compare a native cache's
    saved block hash. Reorged checkpoints are discarded and fully rebuilt. -/
private def checkpointMatches (budget : Budget) (selection : Selection)
    (state : State) (expectedHash : Option ByteArray) : IO Bool := do
  if state.chainId != selection.chainId || state.pool != selection.pool ||
      state.registeredBlock != selection.registeredBlock ||
      state.lastSyncedBlock > selection.head then return false
  let some expectedRoot := state.verifiedRoot | return false
  let (count, root) ← poolClaims budget selection state.lastSyncedBlock
  if count != state.deposits.size || root != expectedRoot then return false
  if let some hash := expectedHash then
    if (← blockHash budget state.lastSyncedBlock) != hash then return false
  return true

/-- Optional pinned asset import and protected native snapshot persistence.
    A malformed present cache or pinned asset fails closed. A structurally
    valid checkpoint that disagrees with current RPC claims is discarded;
    fresh history is replayed instead. RPC truth/finality remain assumptions.
    The cache directory must already be owner-only mode 0700. -/
def syncSelectedPoolWithAssets (transport : Transport) (fresh : State)
    (assetsDir : Option String := none) (cacheDir : Option String := none)
    (useSaga : Bool := true) : IO Result := do
  let expected ← checked <| SelectedPoolBootstrap.freshState fresh.chainId fresh.pool
  if fresh.registeredBlock != expected.registeredBlock ||
      fresh.lastSyncedBlock != expected.lastSyncedBlock ||
      !fresh.deposits.isEmpty || !fresh.withdrawals.isEmpty then
    fail "Snapshot sync requires the pinned fresh selected-pool state."
  let budget ← newBudget transport
  let selection ← captureSelection budget fresh
  let initialHeadHash ← blockHash budget selection.head
  let cached ← match cacheDir with
    | none => pure none
    | some directory => HistorySnapshot.loadCache directory fresh.chainId fresh.pool
  let mut prior := fresh
  let mut found := false
  if let some saved := cached then
    if ← checkpointMatches budget selection saved.state (some saved.blockHash) then
      prior := saved.state
      found := true
  if !found then
    if let some directory := assetsDir then
      if let some pinned ← HistorySnapshot.loadPinned directory fresh.chainId fresh.pool then
        if ← checkpointMatches budget selection pinned none then
          prior := pinned
  let result ← syncWithBudget budget prior useSaga (some { selection with
    lastSyncedBlock := prior.lastSyncedBlock, finalizedBlock := prior.finalizedBlock })
  if (← blockHash budget result.capturedHead) != initialHeadHash then
    fail "The chain changed during cached pool-history synchronization."
  checkDeadline budget
  if let some directory := cacheDir then
    HistorySnapshot.saveCache directory cached result.state initialHeadHash
  return result

private def sagaBase (chainId : Nat) : Except String String :=
  if chainId == 1 then .ok "https://saga.0000000000.org"
  else if chainId == 11155111 then .ok "https://saga.0000000000.org/sepolia"
  else .error "Unsupported Saga network."

/-- Production transport uses one configured HTTPS RPC URL for every chain,
    log and same-block pool call. The Saga proxy is the pinned CLI default. -/
def liveTransport (chainId : Nat) (rpcUrl : String) : Except String Transport := do
  let base ← sagaBase chainId
  return { sagaIndex := HttpTransport.getSagaIndex (base ++ "/index.json"),
           sagaChunk := fun segment =>
             HttpTransport.getSagaChunk (base ++ "/" ++ segment.file) segment.hot,
           rpc := fun id method params => do
             let request ← checked (JsonRpc.encodeRequest id method params)
             let response ← HttpTransport.postHttps rpcUrl request.toUTF8
             let some raw := String.fromUTF8? response
               | fail "Pool-history RPC returned non-UTF-8 bytes."
             return raw,
           nowMs := IO.monoMsNow }

def syncSelectedPoolLive (prior : State) (rpcUrl : String)
    (useSaga : Bool := true) : IO Result := do
  let transport ← checked (liveTransport prior.chainId rpcUrl)
  syncSelectedPool transport prior useSaga

end Tornado.Runtime.HistorySync

#print axioms Tornado.Runtime.HistorySync.acceptComplete_success_fresh
#print axioms Tornado.Runtime.HistorySync.withinAggregateBytes_sound
