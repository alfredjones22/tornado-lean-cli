import Tornado.Protocol.SagaHistory
import Tornado.Protocol.RpcHistory
import Tornado.Crypto.MiMCTree

/-!
Pure, selected-pool replay after an independently validated Saga or RPC read.
The caller supplies the same-block on-chain leaf count and root. Their truth,
the block head, event completeness, and finality are outside this module.
This reducer intentionally rejects ambiguous or inconsistent history rather
than silently replacing duplicate entries as the alpha.38 SDK Map does.
-/

namespace Tornado.Protocol.HistoryReducer

open Tornado.Crypto Tornado.Protocol.Events
open Tornado.Protocol.SagaHistory Tornado.Protocol.RpcHistory

def maxPoolLeaves : Nat := 2 ^ 20
def maxReplayEvents : Nat := 1000000

private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

structure DepositRecord where
  commitment : ByteArray
  leafIndex : Nat
  timestamp : Nat
  blockNumber : Nat
  logIndex : Nat
  /-- Older pinned SDK snapshots omit log indices. Exact receipt evidence
      resolves those records by decoded identity instead of an invented index. -/
  logIndexKnown : Bool := true
  deriving Inhabited

structure WithdrawalRecord where
  nullifierHash : ByteArray
  recipient : Nat
  relayer : Nat
  fee : Nat
  blockNumber : Nat
  logIndex : Nat
  logIndexKnown : Bool := true
  deriving Inhabited

structure State where
  chainId : Nat
  pool : Nat
  registeredBlock : Nat
  lastSyncedBlock : Nat
  finalizedBlock : Option Nat
  verifiedRoot : Option Nat
  deposits : Array DepositRecord
  withdrawals : Array WithdrawalRecord
  deriving Inhabited

structure Batch where
  chainId : Nat
  pool : Nat
  fromBlock : Nat
  toBlock : Nat
  capturedHead : Nat
  finalizedHead : Nat
  onchainClaimBlock : Nat
  onchainLeafCount : Nat
  onchainRoot : Nat
  events : Array ValidatedEvent
  deriving Inhabited

/-- Fresh deployment states start one block before the selected pool's first
    possible event, as in the pinned CLI bootstrap. -/
def emptyState (chainId pool registeredBlock : Nat) : Except String State := do
  if chainId == 0 || pool >= 2 ^ 160 || registeredBlock == 0 then
    throw "Invalid selected pool identity."
  return { chainId := chainId, pool := pool, registeredBlock := registeredBlock,
           lastSyncedBlock := registeredBlock - 1, finalizedBlock := none,
           verifiedRoot := none, deposits := #[], withdrawals := #[] }

/-- Reject malformed cached state before pruning it. In particular, deposit
    indices must be a contiguous sequence in the array's leaf order. -/
def validateState (state : State) : Except String Unit := do
  if state.chainId == 0 || state.pool >= 2 ^ 160 ||
      state.registeredBlock == 0 ||
      state.lastSyncedBlock + 1 < state.registeredBlock ||
      state.deposits.size > maxPoolLeaves ||
      state.withdrawals.size > maxReplayEvents then
    throw "Invalid selected-pool state identity or cursor."
  if let some finalized := state.finalizedBlock then
    if finalized > state.lastSyncedBlock then
      throw "Pool finalized cursor exceeds saved cursor."
  let mut depositKeys : Std.HashSet Nat := {}
  let mut previousDeposit : Option (Nat × Nat × Bool) := none
  for i in [0:state.deposits.size] do
    let record := state.deposits[i]!
    let key := wordNat record.commitment
    if record.commitment.size != 32 || record.leafIndex != i ||
        record.blockNumber < state.registeredBlock ||
        record.blockNumber > state.lastSyncedBlock || depositKeys.contains key then
      throw "Invalid cached pool deposit sequence."
    if let some (block, log, known) := previousDeposit then
      if record.blockNumber < block ||
          (record.blockNumber == block && known && record.logIndexKnown &&
            record.logIndex <= log) then
        throw "Cached pool deposits are out of event order."
    depositKeys := depositKeys.insert key
    previousDeposit := some (record.blockNumber, record.logIndex, record.logIndexKnown)
  let mut spent : Std.HashSet Nat := {}
  for record in state.withdrawals do
    let key := wordNat record.nullifierHash
    if record.nullifierHash.size != 32 ||
        record.blockNumber < state.registeredBlock ||
        record.blockNumber > state.lastSyncedBlock || spent.contains key then
      throw "Invalid cached pool withdrawal set."
    spent := spent.insert key

/-- Appending one deposit cannot skip or repeat a leaf index. -/
def appendDeposit (deposits : Array DepositRecord) (record : DepositRecord) :
    Except String (Array DepositRecord) :=
  if record.leafIndex == deposits.size && deposits.size < maxPoolLeaves then
    .ok (deposits.push record)
  else .error "Pool deposit leaf index is missing, duplicated, or beyond tree capacity."

theorem appendDeposit_success_next_index (deposits result : Array DepositRecord)
    (record : DepositRecord) (h : appendDeposit deposits record = .ok result) :
    record.leafIndex = deposits.size ∧ result.size = deposits.size + 1 := by
  unfold appendDeposit at h
  by_cases hc : record.leafIndex == deposits.size && deposits.size < maxPoolLeaves
  · simp [hc] at h
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1, by simp⟩
  · simp [hc] at h

private def replay (state : State) (batch : Batch) :
    Except String (Array DepositRecord × Array WithdrawalRecord) := do
  let mut deposits := state.deposits.filter (fun item => item.blockNumber < batch.fromBlock)
  let mut withdrawals := state.withdrawals.filter (fun item => item.blockNumber < batch.fromBlock)
  let mut commitments : Std.HashSet Nat := {}
  let mut nullifiers : Std.HashSet Nat := {}
  for item in deposits do commitments := commitments.insert (wordNat item.commitment)
  for item in withdrawals do nullifiers := nullifiers.insert (wordNat item.nullifierHash)
  let mut previous : Option (Nat × Nat) := none
  for event in batch.events do
    if event.blockNumber < batch.fromBlock || event.blockNumber > batch.toBlock ||
        event.log.address != batch.pool then
      throw "History event is outside the selected pool or replay range."
    if let some (block, log) := previous then
      if event.blockNumber < block ||
          (event.blockNumber == block && event.logIndex <= log) then
        throw "Pool history events are not strictly ordered."
    previous := some (event.blockNumber, event.logIndex)
    if event.isDeposit then
      let decoded ← decodeDeposit event.log
      let key := wordNat decoded.commitment
      if commitments.contains key then
        throw "Duplicate pool deposit commitment."
      deposits ← appendDeposit deposits {
        commitment := decoded.commitment, leafIndex := decoded.leafIndex,
        timestamp := decoded.timestamp, blockNumber := event.blockNumber,
        logIndex := event.logIndex }
      commitments := commitments.insert key
    else
      let decoded ← decodeWithdrawal event.log
      let key := wordNat decoded.nullifierHash
      if nullifiers.contains key then
        throw "Duplicate pool withdrawal nullifier."
      withdrawals := withdrawals.push {
        nullifierHash := decoded.nullifierHash,
        recipient := decoded.recipient, relayer := decoded.relayer,
        fee := decoded.fee, blockNumber := event.blockNumber,
        logIndex := event.logIndex }
      nullifiers := nullifiers.insert key
  return (deposits, withdrawals)

private def applyCore (state : State) (batch : Batch) : Except String State := do
  validateState state
  if batch.chainId != state.chainId || batch.pool != state.pool ||
      batch.fromBlock < state.registeredBlock ||
      batch.fromBlock > state.lastSyncedBlock + 1 ||
      batch.fromBlock > batch.toBlock || batch.toBlock < state.lastSyncedBlock ||
      batch.toBlock > batch.capturedHead ||
      batch.onchainClaimBlock != batch.toBlock ||
      batch.events.size > maxReplayEvents ||
      batch.onchainLeafCount > maxPoolLeaves ||
      batch.onchainRoot >= mimcFieldPrime then
    throw "Invalid or incomplete selected-pool replay range."
  if let some finalized := state.finalizedBlock then
    if batch.fromBlock < finalized then
      throw "Replay would replace history before the finalized cursor."
    if batch.finalizedHead < finalized then
      throw "RPC finality claim regressed behind the saved pool cursor."
  let (deposits, withdrawals) ← replay state batch
  if withdrawals.size > maxReplayEvents then
    throw "Pool withdrawal history exceeds native memory budget."
  if deposits.size != batch.onchainLeafCount then
    throw "Synced deposit count differs from the same-block chain claim."
  if !deposits.isEmpty then
    let root ← buildMimcTree (deposits.map (fun item => wordNat item.commitment))
    if root.root != batch.onchainRoot then
      throw "Synced deposit root differs from the same-block chain claim."
  -- Alpha.38 accepts the RPC's empty-tree root directly; there are no
  -- deposits from which to compute an independent nonempty root.
  -- Unlike alpha.38's max(fromBlock, finalizedHead), never mark a block
  -- finalized merely because the scan began there. A stale finality claim
  -- leaves the cursor unset so later replay remains possible.
  let cappedFinalized := min batch.finalizedHead batch.toBlock
  let finalized := if cappedFinalized < state.registeredBlock then none
    else some cappedFinalized
  let result : State := { state with
    lastSyncedBlock := batch.toBlock, finalizedBlock := finalized,
    verifiedRoot := some batch.onchainRoot, deposits, withdrawals }
  validateState result
  return result

/-- An executable postcondition protects consumers if replay internals change.
    The separate theorem shows accepted results satisfy it. -/
def resultBound (input : State) (batch : Batch) (result : State) : Bool :=
  result.chainId == input.chainId && result.pool == input.pool &&
  result.registeredBlock == input.registeredBlock &&
  result.lastSyncedBlock == batch.toBlock &&
  result.deposits.size == batch.onchainLeafCount &&
  result.verifiedRoot == some batch.onchainRoot

def applyBatch (state : State) (batch : Batch) : Except String State :=
  match applyCore state batch with
  | .error message => .error message
  | .ok result =>
      if resultBound state batch result then .ok result
      else .error "Pool replay result failed its identity and same-block postcondition."

theorem applyBatch_success_bound (state result : State) (batch : Batch)
    (h : applyBatch state batch = .ok result) :
    resultBound state batch result = true := by
  cases hc : applyCore state batch with
  | error _ => simp [applyBatch, hc] at h
  | ok candidate =>
      by_cases hb : resultBound state batch candidate = true
      · simp [applyBatch, hc, hb] at h
        cases h
        exact hb
      · simp [applyBatch, hc, hb] at h

theorem applyBatch_success_identity (state result : State) (batch : Batch)
    (h : applyBatch state batch = .ok result) :
    result.chainId = state.chainId ∧ result.pool = state.pool ∧
    result.registeredBlock = state.registeredBlock ∧
    result.lastSyncedBlock = batch.toBlock ∧
    result.deposits.size = batch.onchainLeafCount ∧
    result.verifiedRoot = some batch.onchainRoot := by
  have bound := applyBatch_success_bound state result batch h
  simp only [resultBound, Bool.and_eq_true, beq_iff_eq] at bound
  exact ⟨bound.1.1.1.1.1, bound.1.1.1.1.2,
    bound.1.1.1.2, bound.1.1.2, bound.1.2, bound.2⟩

/-- Adapter from a fully checked Saga chunk set. `applyBatch` still checks the
    event bytes and pool identity because these structures are caller-built. -/
def applySaga (state : State) (selection : Selection)
    (history : ValidatedHistory)
    (finalizedHead onchainClaimBlock onchainLeafCount onchainRoot : Nat) :
    Except String State := do
  if state.chainId != selection.chainId || state.pool != selection.pool ||
      state.registeredBlock != selection.registeredBlock ||
      state.lastSyncedBlock != selection.lastSyncedBlock ||
      history.replayStart != firstReplayBlock selection ||
      history.coverage > selection.head then
    throw "Saga history does not match the selected saved pool."
  applyBatch state { chainId := selection.chainId, pool := selection.pool,
                     fromBlock := history.replayStart, toBlock := history.coverage,
                     capturedHead := selection.head, finalizedHead := finalizedHead,
                     onchainClaimBlock := onchainClaimBlock,
                     onchainLeafCount := onchainLeafCount, onchainRoot := onchainRoot,
                     events := history.events }

/-- Adapter for one validated RPC slice. The caller must request successive
    slices on the same endpoint and capture same-block root/leaf-count claims. -/
def applyRpc (state : State) (selection : Selection) (slice : CheckedSlice)
    (finalizedHead onchainClaimBlock onchainLeafCount onchainRoot : Nat) :
    Except String State := do
  if state.chainId != selection.chainId || state.pool != selection.pool ||
      state.registeredBlock != selection.registeredBlock ||
      state.lastSyncedBlock != selection.lastSyncedBlock ||
      slice.toBlock > selection.head then
    throw "RPC history does not match the selected pool or captured head."
  applyBatch state { chainId := selection.chainId, pool := selection.pool,
                     fromBlock := slice.fromBlock, toBlock := slice.toBlock,
                     capturedHead := selection.head, finalizedHead := finalizedHead,
                     onchainClaimBlock := onchainClaimBlock,
                     onchainLeafCount := onchainLeafCount, onchainRoot := onchainRoot,
                     events := slice.events }

end Tornado.Protocol.HistoryReducer

#print axioms Tornado.Protocol.HistoryReducer.appendDeposit_success_next_index
#print axioms Tornado.Protocol.HistoryReducer.applyBatch_success_bound
#print axioms Tornado.Protocol.HistoryReducer.applyBatch_success_identity
