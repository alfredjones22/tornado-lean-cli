import Tornado.Runtime.HistorySnapshotManifest
import Tornado.Runtime.ProtectedIO
import Tornado.Runtime.JsonRpc
import Tornado.Compression.Gzip
import Tornado.Crypto.SHA256

/-!
Bounded selected-pool public history imports and a protected native cache.
Pinned SDK snapshots are authenticated against compiled descriptor hashes.
Native cache chunks are immutable and content addressed; the small index is
replaced by protected compare-and-replace only after all chunks are durable.
No note, preimage, mnemonic, or selected-note identifier is stored here.
Neither a digest nor a protected file authenticates Ethereum consensus. The
sync caller must recheck the saved checkpoint with its configured RPC.
-/

namespace Tornado.Runtime.HistorySnapshot

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol
open Tornado.Protocol.HistoryReducer Tornado.Runtime.HistorySnapshotManifest

def maxPinnedBytes : Nat := 128 * 1024 * 1024
def maxCacheBytes : Nat := 256 * 1024 * 1024
def maxChunkBytes : Nat := 1024 * 1024
def recordsPerChunk : Nat := 1000
def maxChunks : Nat := 4096

private def bad : String := "Invalid or inconsistent public pool history snapshot."
private def failed : IO α := throw <| IO.userError bad

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error _ => failed

private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def wordBytes (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do
    bytes := bytes.push ((value / 256 ^ (31 - i) % 256).toUInt8)
  return bytes

private def field (value : Json) (key : String) : Except String Json :=
  value.getObjVal? key

private def hexNat (value : Json) : Except String Nat := do
  let raw ← value.getStr?
  if !raw.startsWith "0x" || raw.length <= 2 || raw.length > 66 then throw bad
  -- SDK state uses both quantities and padded byte strings. Normalize only
  -- after checking the original digit count; native cache encoding is checked
  -- separately against its exact canonical serializer.
  let digits := raw.toList.drop 2
  let padded := String.ofList (List.replicate (64 - digits.length) '0' ++ digits)
  let bytes ← Tornado.Domain.parseHexBytes padded
  return wordNat bytes

private def decimal (value : Json) : Except String Nat := do
  let raw ← value.getStr?
  if raw.isEmpty || raw.length > 78 then throw bad
  let some number := raw.toNat? | throw bad
  if toString number != raw then throw bad
  return number

private def hexWord (value : Json) : Except String ByteArray := do
  let number ← hexNat value
  if number >= 2 ^ 256 then throw bad
  return wordBytes number

private def arr (value : Json) : Except String (Array Json) := value.getArr?

private def pair (value : Json) : Except String (Json × Json) := do
  let values ← arr value
  if values.size != 2 then throw bad
  return (values[0]!, values[1]!)

private def selectedRow (state : State) : Except String SelectedPoolBootstrap.Row := do
  let row ← SelectedPoolBootstrap.byIdentity state.chainId state.pool
  if row.registeredBlock != state.registeredBlock then throw bad
  return row

private def validateShape (state : State) : Except String Unit := do
  let row ← selectedRow state
  validateState state
  if state.lastSyncedBlock >= 2 ^ 64 then throw bad
  for record in state.deposits do
    if wordNat record.commitment >= mimcFieldPrime || record.timestamp >= 2 ^ 64 ||
        record.logIndex >= 2 ^ 32 then throw bad
  for record in state.withdrawals do
    if wordNat record.nullifierHash >= mimcFieldPrime ||
        record.recipient == 0 || record.recipient >= 2 ^ 160 ||
        record.relayer >= 2 ^ 160 || record.fee > row.amount ||
        record.logIndex >= 2 ^ 32 then throw bad
  return ()

/-- Validate native state and recompute its deposit root. Withdrawals do not
    contribute to that root; selected-note spent/receipt checks remain required. -/
def validate (state : State) : Except String Unit := do
  validateShape state
  let tree ← buildMimcTree (state.deposits.map (fun item => wordNat item.commitment))
  if state.verifiedRoot != some tree.root then throw bad

private def optionalPinnedLog (value : Json) : Except String (Nat × Bool) := do
  match value.getObjVal? "logIndex" with
  | .error _ => return (0, false)
  | .ok log =>
    let number ← match log with
      | .str _ => hexNat log
      | _ => log.getNat?
    if number >= 2 ^ 32 then throw bad
    return (number, true)

/-- Parse only the selected pool from an already authenticated SDK snapshot.
    The omitted historical log index is marked unknown, never fabricated. -/
def decodePinnedJson (descriptor : Descriptor) (raw : String) : Except String State := do
  let json ← Json.parse raw
  let object ← json.getObj?
  if object.size != 1 then throw bad
  let body ← field json descriptor.stateKey
  let chain ← hexNat (← field (← field body "instanceRegistryInfo") "chainId")
  if chain != descriptor.chainId then throw bad
  let row ← SelectedPoolBootstrap.byIdentity chain descriptor.pool
  let pools ← arr (← field (← field body "pools") "poolsTuples")
  if pools.size != 1 then throw bad
  let (key, pool) ← pair pools[0]!
  if (← hexNat key) != descriptor.pool ||
      (← hexNat (← field pool "address")) != descriptor.pool ||
      (← hexNat (← field pool "denomination")) != row.amount ||
      (← hexNat (← field pool "asset")) != row.asset ||
      (← (← field pool "isERC20").getBool?) != (row.asset != 0) ||
      (← hexNat (← field pool "registeredBlock")) != row.registeredBlock ||
      (← hexNat (← field pool "lastSyncedBlock")) != descriptor.toBlock ||
      row.registeredBlock != descriptor.fromBlock then throw bad
  let depositGroups ← arr (← field (← field body "deposits") "depositsTuples")
  if depositGroups.size > 1 then throw bad
  let entries ← if depositGroups.isEmpty then pure #[] else do
    let (address, records) ← pair depositGroups[0]!
    if (← hexNat address) != descriptor.pool then throw bad
    arr records
  if entries.size != descriptor.deposits || entries.size > maxPoolLeaves then throw bad
  let mut deposits := #[]
  for entry in entries do
    let (key, value) ← pair entry
    let commitment ← hexWord (← field value "commitment")
    if (← hexWord key) != commitment ||
        (← hexNat (← field value "pool")) != descriptor.pool then throw bad
    let (logIndex, known) ← optionalPinnedLog value
    deposits := deposits.push {
      commitment, leafIndex := ← (← field value "leafIndex").getNat?,
      timestamp := ← hexNat (← field value "timestamp"),
      blockNumber := ← hexNat (← field value "blockNumber"),
      logIndex, logIndexKnown := known }
  let entries ← arr (← field (← field body "withdrawals") "withdrawalsTuples")
  if entries.size != descriptor.withdrawals || entries.size > maxReplayEvents then throw bad
  let mut withdrawals := #[]
  for entry in entries do
    let (key, value) ← pair entry
    let nullifierHash ← hexWord (← field value "nullifierHash")
    if (← hexWord key) != nullifierHash ||
        (← hexNat (← field value "pool")) != descriptor.pool then throw bad
    let (logIndex, known) ← optionalPinnedLog value
    withdrawals := withdrawals.push {
      nullifierHash, recipient := ← hexNat (← field value "to"),
      relayer := ← hexNat (← field value "relayer"),
      fee := ← hexNat (← field value "fee"),
      blockNumber := ← hexNat (← field value "blockNumber"),
      logIndex, logIndexKnown := known }
  let tree ← buildMimcTree (deposits.map (fun item => wordNat item.commitment))
  let state : State := {
    chainId := chain, pool := descriptor.pool,
    registeredBlock := row.registeredBlock, lastSyncedBlock := descriptor.toBlock,
    finalizedBlock := none, verifiedRoot := some tree.root, deposits, withdrawals }
  -- The root above was constructed from these exact deposits. Avoid a second
  -- full tree build while retaining all native state and event-shape checks.
  validateShape state
  return state

def decodePinned (descriptor : Descriptor) (bytes : ByteArray) : Except String State := do
  if descriptor.jsonBytes > maxPinnedBytes || descriptor.gzipBytes > maxPinnedBytes ||
      bytes.size > max descriptor.jsonBytes descriptor.gzipBytes then throw bad
  let raw ← if bytes[0]? == some 0x1f && bytes[1]? == some 0x8b then
      Tornado.Compression.Gzip.decompress bytes descriptor.jsonBytes
    else pure bytes
  if raw.size != descriptor.jsonBytes || sha256Hex raw != descriptor.sha256 then throw bad
  let some text := String.fromUTF8? raw | throw bad
  decodePinnedJson descriptor text

private def readBoundedPublic (path : System.FilePath) (limit : Nat) : IO ByteArray := do
  let metadata ← path.symlinkMetadata
  if metadata.type != .file || metadata.byteSize.toNat > limit then failed
  let handle ← IO.FS.Handle.mk path .read
  let mut bytes := ByteArray.empty
  while bytes.size <= limit do
    let chunk ← handle.read (min 65536 (limit + 1 - bytes.size)).toUSize
    if chunk.isEmpty then return bytes
    bytes := bytes ++ chunk
    if bytes.size > limit then failed
  failed

/-- Missing pinned files allow full Saga/RPC rebuild. A present but malformed
    file fails closed rather than silently becoming an accepted cache. -/
def loadPinned (assetsRoot : String) (chainId pool : Nat) : IO (Option State) := do
  let _ ← checked <| SelectedPoolBootstrap.byIdentity chainId pool
  let some descriptor := descriptors.find? (fun row => row.chainId == chainId && row.pool == pool)
    | failed
  let current ← IO.currentDir
  let root := System.FilePath.mk assetsRoot
  let root := if root.isAbsolute then root else current / root
  let path := root / "history" / descriptor.file
  if !(← path.pathExists) then return none
  let bytes ← readBoundedPublic path (max descriptor.jsonBytes descriptor.gzipBytes)
  return some (← checked <| decodePinned descriptor bytes)

private def depositJson (value : DepositRecord) : Json := Json.arr #[
  toJson ("0x" ++ bytesToHex value.commitment), toJson (toString value.leafIndex),
  toJson (toString value.timestamp), toJson (toString value.blockNumber),
  toJson (toString value.logIndex), toJson value.logIndexKnown]

private def withdrawalJson (value : WithdrawalRecord) : Json := Json.arr #[
  toJson ("0x" ++ bytesToHex value.nullifierHash), toJson (toString value.recipient),
  toJson (toString value.relayer), toJson (toString value.fee),
  toJson (toString value.blockNumber), toJson (toString value.logIndex),
  toJson value.logIndexKnown]

private def decodeDeposit (json : Json) : Except String DepositRecord := do
  let values ← arr json
  if values.size != 6 then throw bad
  let value : DepositRecord := {
    commitment := ← hexWord values[0]!, leafIndex := ← decimal values[1]!,
    timestamp := ← decimal values[2]!, blockNumber := ← decimal values[3]!,
    logIndex := ← decimal values[4]!, logIndexKnown := ← values[5]!.getBool? }
  if depositJson value != json then throw bad
  return value

private def decodeWithdrawal (json : Json) : Except String WithdrawalRecord := do
  let values ← arr json
  if values.size != 7 then throw bad
  let value : WithdrawalRecord := {
    nullifierHash := ← hexWord values[0]!, recipient := ← decimal values[1]!,
    relayer := ← decimal values[2]!, fee := ← decimal values[3]!,
    blockNumber := ← decimal values[4]!, logIndex := ← decimal values[5]!,
    logIndexKnown := ← values[6]!.getBool? }
  if withdrawalJson value != json then throw bad
  return value

structure Chunk where
  kind : String
  digest : String
  bytes : Nat
  count : Nat
  deriving Inhabited

private def chunkJson (chunk : Chunk) : Json := Json.arr #[
  toJson chunk.kind, toJson chunk.digest, toJson chunk.bytes, toJson chunk.count]

private def decodeChunk (json : Json) : Except String Chunk := do
  let values ← arr json
  if values.size != 4 then throw bad
  let chunk : Chunk := {
    kind := ← values[0]!.getStr?, digest := ← values[1]!.getStr?,
    bytes := ← values[2]!.getNat?, count := ← values[3]!.getNat? }
  let digest ← parseHexBytes chunk.digest
  if (chunk.kind != "deposits" && chunk.kind != "withdrawals") ||
      digest.size != 32 || bytesToHex digest != chunk.digest ||
      chunk.bytes > maxChunkBytes || chunk.count == 0 || chunk.count > recordsPerChunk then throw bad
  return chunk

structure Cache where
  state : State
  blockHash : ByteArray
  indexBytes : ByteArray

private def indexJson (state : State) (blockHash : ByteArray) (chunks : Array Chunk) : Json :=
  Json.mkObj [
    ("version", toJson (1 : Nat)), ("chainId", toJson (toString state.chainId)),
    ("pool", toJson (toString state.pool)),
    ("registeredBlock", toJson (toString state.registeredBlock)),
    ("lastSyncedBlock", toJson (toString state.lastSyncedBlock)),
    ("root", toJson (toString (state.verifiedRoot.getD 0))),
    ("blockHash", toJson ("0x" ++ bytesToHex blockHash)),
    ("deposits", toJson state.deposits.size),
    ("withdrawals", toJson state.withdrawals.size),
    ("chunks", Json.arr (chunks.map chunkJson))]

private def indexPath (directory : String) (chainId pool : Nat) : String :=
  directory ++ "/history-" ++ toString chainId ++ "-" ++
    bytesToHex ((wordBytes pool).extract 12 32) ++ ".json"

private def chunkPath (directory digest : String) : String :=
  directory ++ "/history-chunk-" ++ digest ++ ".json"

private def absoluteDirectory (directory : String) : IO String := do
  let path := System.FilePath.mk directory
  let current ← IO.currentDir
  let path := if path.isAbsolute then path else current / path
  return path.toString

/-- Load a canonical index and protected immutable chunks. No cached
    finalized cursor is accepted; every later sync replays the overlap. -/
def loadCache (directory : String) (chainId pool : Nat) : IO (Option Cache) := do
  let directory ← absoluteDirectory directory
  ProtectedIO.checkPrivateDirectory directory
  let path := indexPath directory chainId pool
  if !(← (System.FilePath.mk path).pathExists) then return none
  let bytes ← ProtectedIO.readPrivate path
  let some raw := String.fromUTF8? bytes | failed
  let json ← checked <| Json.parse raw
  if (← checked <| (← checked <| field json "version").getNat?) != 1 then failed
  let savedChain ← checked <| decimal (← checked <| field json "chainId")
  let savedPool ← checked <| decimal (← checked <| field json "pool")
  if savedChain != chainId || savedPool != pool then failed
  let registeredBlock ← checked <| decimal (← checked <| field json "registeredBlock")
  let cursor ← checked <| decimal (← checked <| field json "lastSyncedBlock")
  let root ← checked <| decimal (← checked <| field json "root")
  let blockHash ← checked <| hexWord (← checked <| field json "blockHash")
  let depositCount ← checked <| (← checked <| field json "deposits").getNat?
  let withdrawalCount ← checked <| (← checked <| field json "withdrawals").getNat?
  if depositCount > maxPoolLeaves || withdrawalCount > maxReplayEvents then failed
  let rows ← checked <| arr (← checked <| field json "chunks")
  if rows.size > maxChunks then failed
  let chunks ← checked <| rows.mapM decodeChunk
  let mut deposits := #[]
  let mut withdrawals := #[]
  let mut total := 0
  for chunk in chunks do
    total := total + chunk.bytes
    if total > maxCacheBytes then failed
    let bytes ← ProtectedIO.readPrivate (chunkPath directory chunk.digest)
    if bytes.size != chunk.bytes || sha256Hex bytes != chunk.digest then failed
    let some text := String.fromUTF8? bytes | failed
    let json ← checked <| Json.parse text
    let entries ← checked <| arr json
    if entries.size != chunk.count then failed
    if chunk.kind == "deposits" then
      if deposits.size + entries.size > depositCount then failed
      let parsed ← checked <| entries.mapM decodeDeposit
      if (Json.arr (parsed.map depositJson)).compress != text then failed
      deposits := deposits ++ parsed
    else
      if withdrawals.size + entries.size > withdrawalCount then failed
      let parsed ← checked <| entries.mapM decodeWithdrawal
      if (Json.arr (parsed.map withdrawalJson)).compress != text then failed
      withdrawals := withdrawals ++ parsed
  if deposits.size != depositCount || withdrawals.size != withdrawalCount then failed
  let state : State := {
    chainId, pool, registeredBlock, lastSyncedBlock := cursor,
    finalizedBlock := none, verifiedRoot := some root, deposits, withdrawals }
  if (indexJson state blockHash chunks).compress != raw then failed
  let _ ← checked <| validate state
  return some ⟨state, blockHash, bytes⟩

private def makeChunks (kind : String) (records : Array Json) : Array (Chunk × ByteArray) := Id.run do
  let mut chunks := #[]
  let mut offset := 0
  while offset < records.size do
    let end_ := min records.size (offset + recordsPerChunk)
    let bytes := (Json.arr (records.extract offset end_)).compress.toUTF8
    chunks := chunks.push (⟨kind, sha256Hex bytes, bytes.size, end_ - offset⟩, bytes)
    offset := end_
  return chunks

/-- Commit immutable protected chunks first, then atomically publish one
    canonical index. Concurrent or stale writers fail the index CAS. -/
def saveCache (directory : String) (previous : Option Cache)
    (state : State) (blockHash : ByteArray) : IO Unit := do
  let directory ← absoluteDirectory directory
  ProtectedIO.checkPrivateDirectory directory
  let _ ← checked <| validate state
  if blockHash.size != 32 then failed
  if let some old := previous then
    if old.state.chainId != state.chainId || old.state.pool != state.pool then failed
  let chunks := makeChunks "deposits" (state.deposits.map depositJson) ++
    makeChunks "withdrawals" (state.withdrawals.map withdrawalJson)
  if chunks.size > maxChunks ||
      chunks.foldl (fun total row => total + row.2.size) 0 > maxCacheBytes then failed
  for (chunk, bytes) in chunks do
    if bytes.size > maxChunkBytes then failed
    let path := chunkPath directory chunk.digest
    if ← (System.FilePath.mk path).pathExists then
      if (← ProtectedIO.readPrivate path) != bytes then failed
    else
      -- A concurrent writer may have created the same content-addressed
      -- chunk. Accept it only after reading the exact expected bytes.
      try ProtectedIO.createPrivate path bytes
      catch _ =>
        if (← ProtectedIO.readPrivate path) != bytes then failed
  let index := (indexJson state blockHash (chunks.map (·.1))).compress.toUTF8
  if index.size > maxChunkBytes then failed
  let path := indexPath directory state.chainId state.pool
  match previous with
  | none => ProtectedIO.createPrivate path index
  | some old => ProtectedIO.replacePrivate path old.indexBytes index

end Tornado.Runtime.HistorySnapshot
