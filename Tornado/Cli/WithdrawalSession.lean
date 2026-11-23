import Tornado.Cli.History
import Tornado.Protocol.ProverWorkerWire
import Tornado.Runtime.HttpTransport

/-! Public-only note preparation shared by sponsored and classic-relayer
withdrawals. The protected backup is inspected and proved only in the worker;
this parent session contains no note or secret preimage. Public identifiers
are privacy sensitive as an association and must not be logged or cached. -/

namespace Tornado.Cli.WithdrawalSession

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire

structure Session where
  metadata : Metadata
  pool : Pool
  history : HistorySync.Result
  capturedBlockHash : ByteArray
  spentAtHead : Bool
  leafIndex : Nat

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

def resolvePool (metadata : Metadata) : Except String Pool := do
  metadata.validate
  let some chain := chainFromNat metadata.chainId
    | throw "Unsupported selected-note network."
  let some pool := allPools.find? (fun pool => pool.chainId == chain &&
    (parseHexBytes pool.address).toOption.map wordNat == some metadata.pool)
    | throw "Selected note is outside the pinned pool catalog."
  let _ ← SelectedPoolBootstrap.selected metadata.chainId pool
  return pool

def inspectWith (transport : HistorySync.Transport) (metadata : Metadata)
    (assetsDir cacheDir : Option String := none) : IO Session := do
  let pool ← checked <| resolvePool metadata
  let evidence ← History.inspectPublic transport pool
    (← checked <| Abi.uintWord metadata.commitment)
    (← checked <| Abi.uintWord metadata.nullifierHash) assetsDir cacheDir
  if evidence.spentAtHead then
    throw <| IO.userError "Selected note is already spent."
  return {
    metadata, pool, history := evidence.history
    capturedBlockHash := evidence.capturedBlockHash, spentAtHead := false,
    leafIndex := evidence.leafIndex }

def inspectLive (rpcUrl : String) (metadata : Metadata)
    (assetsDir cacheDir : Option String := none) : IO Session := do
  let transport ← checked <| HistorySync.liveTransport metadata.chainId rpcUrl
  inspectWith transport metadata assetsDir cacheDir

/-- Synchronize each distinct pool once, but verify every selected note's
exact deposit receipt and spent evidence against that shared captured head. -/
def inspectManyWith (transport : HistorySync.Transport) (metadata : Array Metadata)
    (assetsDir cacheDir : Option String := none) : IO (Array Session) := do
  checked <| BatchMetadata.validate metadata
  let mut pools : Array (Nat × History.SyncedSelection) := #[]
  let mut sessions := #[]
  for note in metadata do
    let pool ← checked <| resolvePool note
    let selected ← match pools.find? (fun row => row.1 == note.pool) with
      | some row => pure row.2
      | none => do
        let value ← History.syncPublic transport pool assetsDir cacheDir
        pools := pools.push (note.pool, value)
        pure value
    let evidence ← History.inspectPublicFromSynced transport selected
      (← checked <| Abi.uintWord note.commitment)
      (← checked <| Abi.uintWord note.nullifierHash)
    if evidence.spentAtHead then throw <| IO.userError "Selected note is already spent."
    sessions := sessions.push {
      metadata := note, pool, history := evidence.history
      capturedBlockHash := evidence.capturedBlockHash, spentAtHead := false
      leafIndex := evidence.leafIndex }
  return sessions

def inspectManyLive (rpcUrl : String) (metadata : Array Metadata)
    (assetsDir cacheDir : Option String := none) : IO (Array Session) := do
  checked <| BatchMetadata.validate metadata
  let transport ← checked <| HistorySync.liveTransport metadata[0]!.chainId rpcUrl
  inspectManyWith transport metadata assetsDir cacheDir

/-- Reconstruct the circuit path from the same complete history whose root,
leaf count, selected receipt and unspent status were checked at one head. -/
private def requestWithTree (session : Session) (recipient relayer fee : Nat)
    (tree : MimcTree) :
    Except String Request := do
  let pool ← resolvePool session.metadata
  let state := session.history.state
  HistoryReducer.validateState state
  if pool != session.pool || session.spentAtHead ||
      session.capturedBlockHash.size != 32 ||
      state.chainId != session.metadata.chainId || state.pool != session.metadata.pool ||
      state.lastSyncedBlock != session.history.capturedHead ||
      state.lastSyncedBlock < state.registeredBlock || fee >= pool.amount ||
      ((fee == 0) != (relayer == 0)) then
    throw "Selected note, history or payout policy differs from review."
  let some root := state.verifiedRoot
    | throw "Selected history has no same-block verified root."
  let commitment ← Abi.uintWord session.metadata.commitment
  let nullifier ← Abi.uintWord session.metadata.nullifierHash
  let found := state.deposits.filter (fun row => row.commitment == commitment)
  if found.size != 1 || found[0]!.leafIndex != session.leafIndex ||
      session.leafIndex >= state.deposits.size ||
      state.deposits[session.leafIndex]!.commitment != commitment ||
      state.withdrawals.any (fun row => row.nullifierHash == nullifier) then
    throw "Selected note has no unique unspent deposit in complete history."
  if tree.root != root || tree.layers[0]? !=
      some (state.deposits.map (fun row => wordNat row.commitment)) then
    throw "Selected history tree differs from the same-block pool root."
  let path ← mimcProofAt tree session.leafIndex
  let request : Request := {
    chainId := session.metadata.chainId, pool := session.metadata.pool,
    commitment := session.metadata.commitment, nullifierHash := session.metadata.nullifierHash,
    leafIndex := path.index, root := path.root, siblings := path.siblings,
    pathIndices := path.pathIndices, recipient, relayer, fee, refund := 0 }
  request.validate
  return request

def requestFor (session : Session) (recipient relayer fee : Nat) :
    Except String Request := do
  let tree ← buildMimcTree (session.history.state.deposits.map
    (fun row => wordNat row.commitment))
  requestWithTree session recipient relayer fee tree

/-- Initial zero-fee requests for estimation. MiMC layers are built once per
pool; each session must still bind to the exact same captured snapshot and
full leaf array before its ordered path can be extracted. -/
def requestsMany (sessions : Array Session) (recipient : Nat) : Except String (Array Request) := do
  BatchMetadata.validate (sessions.map (·.metadata))
  let mut trees : Array (Nat × Nat × ByteArray × MimcTree) := #[]
  let mut requests := #[]
  for session in sessions do
    let pool := session.metadata.pool
    let tree ← match trees.find? (fun row => row.1 == pool) with
      | some (_, head, blockHash, tree) => do
        if head != session.history.capturedHead || blockHash != session.capturedBlockHash then
          throw "Same-pool notes do not share one captured history."
        pure tree
      | none => do
        let tree ← buildMimcTree (session.history.state.deposits.map
          (fun row => wordNat row.commitment))
        trees := trees.push (pool, session.history.capturedHead, session.capturedBlockHash, tree)
        pure tree
    requests := requests.push (← requestWithTree session recipient 0 0 tree)
  return requests

private def quantity (n : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 n)

private def address (n : Nat) : Except String String := do
  return "0x" ++ bytesToHex ((← Abi.addressWord n).extract 12 32)

/-- Recheck at a fresh exact block. A normally advanced root remains usable
while isKnownRoot(originalRoot) is true. Reorgs of the prepared history and
already-spent notes fail closed. RPC messages are never reflected. -/
def revalidateWith (transport : HistorySync.Transport) (session : Session) : IO Unit := do
  try
    let _ ← checked <| resolvePool session.metadata
    let state := session.history.state
    if state.chainId != session.metadata.chainId || state.pool != session.metadata.pool ||
        state.lastSyncedBlock != session.history.capturedHead ||
        session.capturedBlockHash.size != 32 || session.spentAtHead then
      throw <| IO.userError "Invalid selected withdrawal session."
    let some root := state.verifiedRoot
      | throw <| IO.userError "Missing selected pool root."
    let ids ← IO.mkRef 18000
    let rpc (method : JsonRpc.Method) (params : Array Json) : IO Json := do
      let id ← ids.get
      ids.set (id + 1)
      let raw ← transport.rpc id method params
      if raw.utf8ByteSize > RpcHistory.maxRpcResponseBytes then
        throw <| IO.userError "Selected-note response exceeds its limit."
      checked <| JsonRpc.parseResult id raw
    let checkChain : IO Unit := do
      let chain ← checked <| JsonRpc.parseHexQuantity (← checked (← rpc .chainId #[]).getStr?)
      if chain != session.metadata.chainId then throw <| IO.userError "Chain changed."
    let blockHash (number : Nat) : IO ByteArray := do
      let block ← rpc .getBlockByNumber #[toJson (quantity number), toJson false]
      let reported ← checked <| JsonRpc.parseHexQuantity
        (← checked (← checked <| block.getObjVal? "number").getStr?)
      let raw ← checked (← checked <| block.getObjVal? "hash").getStr?
      let bytes ← checked <| parseHexBytes raw
      if reported != number || !raw.startsWith "0x" || bytes.size != 32 then
        throw <| IO.userError "Invalid block identity."
      return bytes
    checkChain
    let latest ← checked <| JsonRpc.parseHexQuantity (← checked (← rpc .blockNumber #[]).getStr?)
    if latest < session.history.capturedHead then throw <| IO.userError "Chain moved backwards."
    let latestHash ← blockHash latest
    if (← blockHash session.history.capturedHead) != session.capturedBlockHash then
      throw <| IO.userError "Prepared history was reorganized."
    let callWord (signature : String) (tail : ByteArray) : IO Nat := do
      let result ← rpc .call #[Json.mkObj [
        ("to", toJson (← checked <| address state.pool)),
        ("data", toJson ("0x" ++ bytesToHex (Abi.selector signature ++ tail)))],
        toJson (quantity latest)]
      let raw ← checked result.getStr?
      let bytes ← checked <| parseHexBytes raw
      if !raw.startsWith "0x" || bytes.size != 32 then
        throw <| IO.userError "Invalid selected-pool word."
      return wordNat bytes
    if (← callWord "isKnownRoot(bytes32)" (← checked <| Abi.uintWord root)) != 1 then
      throw <| IO.userError "Prepared root is no longer accepted."
    if (← callWord "isSpent(bytes32)" (← checked <| Abi.uintWord session.metadata.nullifierHash)) != 0 then
      throw <| IO.userError "Selected note is spent."
    if (← callWord "nextIndex()" ByteArray.empty) < state.deposits.size then
      throw <| IO.userError "Pool leaf count moved backwards."
    checkChain
    if (← blockHash latest) != latestHash then throw <| IO.userError "Chain changed."
  catch _ => throw <| IO.userError "Selected-note live revalidation failed."

def revalidateLive (rpcUrl : String) (session : Session) : IO Unit := do
  let transport ← checked <| HistorySync.liveTransport session.metadata.chainId rpcUrl
  revalidateWith transport session

end Tornado.Cli.WithdrawalSession
