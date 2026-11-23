import Lean
import Tornado.Crypto.SHA256
import Tornado.Domain.NoteIdentity
import Tornado.Protocol.Events
import Tornado.Runtime.JsonRpc
import Tornado.Compression.Gzip

/-!
Pure, bounded validator for the pinned CLI's Saga Tornado pool history format.
The caller must separately authenticate its HTTPS/RPC endpoints, obtain a
chain-matched snapshot and a captured head, and fall back to RPC on any error.
No coverage is returned until every selected chunk has passed all checks.
-/

namespace Tornado.Protocol.SagaHistory

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol.Events

def legacyRewindBlocks : Nat := 7200
def maxIndexBytes : Nat := 2 * 1024 * 1024
def maxCompressedChunkBytes : Nat := 32 * 1024 * 1024
def maxDecodedChunkBytes : Nat := 32 * 1024 * 1024
def maxEventsPerChunk : Nat := 1000000
def maxSelectedSegments : Nat := 64
def maxAggregateCompressedBytes : Nat := 256 * 1024 * 1024
def maxSelectedEvents : Nat := 1000000

def withinSegmentBudget (count : Nat) : Bool :=
  count ≤ maxSelectedSegments

def withinByteSizeBudget (sizes : Array Nat) : Bool :=
  sizes.foldl (· + ·) 0 ≤ maxAggregateCompressedBytes

def withinChunkByteBudget (chunks : Array ByteArray) : Bool :=
  withinByteSizeBudget (chunks.map (·.size))

structure Selection where
  chainId : Nat
  pool : Nat
  registeredBlock : Nat
  lastSyncedBlock : Nat
  finalizedBlock : Option Nat := none
  head : Nat
  deriving Repr, Inhabited

/-- Alpha.38 rewind rule. Nat subtraction saturates at zero; `max` with the
    registered block agrees with the TypeScript BigInt rule for valid pools. -/
def firstReplayBlock (selection : Selection) : Nat :=
  let finalized := selection.finalizedBlock.getD
    (selection.lastSyncedBlock - legacyRewindBlocks)
  max selection.registeredBlock (min finalized selection.lastSyncedBlock)

theorem replay_never_before_registration (selection : Selection) :
    selection.registeredBlock ≤ firstReplayBlock selection := by
  exact Nat.le_max_left _ _

/-- A fresh cache cursor before registration starts replay at registration. -/
theorem cursor_before_registration_replay (selection : Selection)
    (hcursor : selection.lastSyncedBlock ≤ selection.registeredBlock) :
    firstReplayBlock selection = selection.registeredBlock := by
  unfold firstReplayBlock
  apply Nat.max_eq_left
  exact Nat.le_trans (Nat.min_le_right _ _) hcursor

structure Segment where
  fromBlock : Nat
  toBlock : Nat
  file : String
  digest : String
  hot : Bool := false
  deriving Repr, Inhabited

structure Plan where
  selection : Selection
  replayStart : Nat
  coverage : Nat
  trackedAddresses : Array Nat
  transactionHashField : Bool
  segments : Array Segment
  deriving Inhabited

structure ValidatedEvent where
  blockNumber : Nat
  logIndex : Nat
  log : Log
  isDeposit : Bool
  deriving Inhabited

structure ValidatedHistory where
  replayStart : Nat
  coverage : Nat
  events : Array ValidatedEvent
  deriving Inhabited

structure SyncedPool where
  chainId : Nat
  pool : Nat
  lastSyncedBlock : Nat
  deriving Repr, Inhabited

private def invalid : String := "Invalid Saga history."

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

private def hexAddress (raw : String) : Except String Nat := do
  let bytes ← fixedHex raw 20
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def checkedAddress (json : Json) (name : String) : Except String Nat :=
  (string json name).bind hexAddress

private def asArray (json : Json) : Except String (Array Json) :=
  json.getArr? |>.mapError (fun _ => invalid)

private def asciiAlphaNum (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9')

private def validFile (path : String) : Bool := Id.run do
  let pieces := path.splitOn "/"
  if pieces.isEmpty || pieces.any (· == "..") then return false
  let dirs := pieces.dropLast
  if !dirs.all (fun part => !part.isEmpty && part.toList.all
      (fun c => asciiAlphaNum c || c == '_' || c == '-')) then return false
  let leaf := pieces.getLast!
  if !leaf.endsWith ".jsonl.gz" || leaf.length ≤ ".jsonl.gz".length then
    return false
  return leaf.toList.all (fun c => asciiAlphaNum c ||
    c == '_' || c == '.' || c == '[' || c == ']' || c == '(' ||
    c == ')' || c == ',' || c == '-')

private def validDigest (raw : String) : Bool :=
  let chars := if raw.startsWith "0x" then raw.toList.drop 2 else raw.toList
  chars.length == 64 && chars.all (fun c =>
    ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') ||
    ('A' ≤ c && c ≤ 'F'))

private def parseSegment (hot : Bool) (json : Json) : Except String Segment := do
  let fromBlock ← quantity json "fromBlock"
  let toBlock ← quantity json "toBlock"
  let file ← string json "file"
  let digestObj ← field json "digest"
  if (← string digestObj "type") != "sha256" then throw invalid
  let digest ← string digestObj "data"
  if !validFile file || !validDigest digest then throw invalid
  return { fromBlock, toBlock, file, digest := digest.toLower.replace "0x" "", hot }

private def optionalField (json : Json) (name : String) : Option Json :=
  (json.getObjVal? name).toOption

private def tracked (json : Json) : Except String (Array Nat) := do
  let raw ← asArray (← field json "trackedAddresses")
  raw.mapM fun item => do
    let address ← item.getStr? |>.mapError (fun _ => invalid)
    hexAddress address

private def extraFields (json : Json) : Except String Bool := do
  let some value := optionalField json "extraLogFields" | return false
  let fields ← asArray value
  let mut hasHash := false
  for item in fields do
    let name ← item.getStr? |>.mapError (fun _ => invalid)
    if name != "transactionHash" then throw invalid
    hasHash := true
  return hasHash

private def entryMatches (selection : Selection) (json : Json) : Except String Bool := do
  let some protocol := optionalField json "protocol" | return false
  if (← protocol.getStr? |>.mapError (fun _ => invalid)) != "tornado-cash" then
    return false
  let chain ← quantity json "chainId"
  if chain != selection.chainId then return false
  return (← tracked json).contains selection.pool

/-- The first selected segment may overlap the replay start. All later
    segments must start exactly where the previous one ends. -/
def exactTail : Nat → List Segment → Prop
  | _, [] => True
  | cursor, segment :: rest =>
      segment.fromBlock = cursor ∧ cursor < segment.toBlock ∧
        exactTail segment.toBlock rest

def continuousCoverage (first : Nat) : List Segment → Prop
  | [] => False
  | segment :: rest =>
      segment.fromBlock ≤ first ∧ first < segment.toBlock ∧
        exactTail segment.toBlock rest

private def validateTail (cursor : Nat) : List Segment → Except String Nat
  | [] => .ok cursor
  | segment :: rest =>
      if segment.fromBlock = cursor ∧ cursor < segment.toBlock then
        validateTail segment.toBlock rest
      else .error "Gap or overlap in Saga coverage."

def validateCoverage (first : Nat) : List Segment → Except String Nat
  | [] => .error "Saga does not cover the required pool rewind."
  | segment :: rest =>
      if segment.fromBlock ≤ first ∧ first < segment.toBlock then
        validateTail segment.toBlock rest
      else .error "Gap or overlap in Saga coverage."

private theorem validateTail_sound (cursor : Nat) (segments : List Segment)
    (endBlock : Nat) (h : validateTail cursor segments = .ok endBlock) :
    exactTail cursor segments := by
  induction segments generalizing cursor with
  | nil => trivial
  | cons segment rest ih =>
      by_cases hc : segment.fromBlock = cursor ∧ cursor < segment.toBlock
      · simp only [validateTail, if_pos hc] at h
        exact ⟨hc.1, hc.2, ih segment.toBlock h⟩
      · simp [validateTail, hc] at h

private theorem validateTail_end (cursor : Nat) (segments : List Segment)
    (endBlock : Nat) (h : validateTail cursor segments = .ok endBlock) :
    cursor ≤ endBlock := by
  induction segments generalizing cursor with
  | nil =>
      simp only [validateTail, Except.ok.injEq] at h
      omega
  | cons segment rest ih =>
      by_cases hc : segment.fromBlock = cursor ∧ cursor < segment.toBlock
      · simp only [validateTail, if_pos hc] at h
        exact Nat.le_trans (Nat.le_of_lt hc.2) (ih segment.toBlock h)
      · simp [validateTail, hc] at h

/-- Successful coverage validation entails the initial overlap and exact
    adjacency of every later chunk. This is independent of index provenance. -/
theorem validate_coverage_sound (first : Nat) (segments : List Segment)
    (endBlock : Nat) (h : validateCoverage first segments = .ok endBlock) :
    continuousCoverage first segments := by
  cases segments with
  | nil => simp [validateCoverage] at h
  | cons segment rest =>
      by_cases hc : segment.fromBlock ≤ first ∧ first < segment.toBlock
      · simp only [validateCoverage, if_pos hc] at h
        exact ⟨hc.1, hc.2, validateTail_sound segment.toBlock rest endBlock h⟩
      · simp [validateCoverage, hc] at h

theorem validate_coverage_end (first : Nat) (segments : List Segment)
    (endBlock : Nat) (h : validateCoverage first segments = .ok endBlock) :
    first < endBlock := by
  cases segments with
  | nil => simp [validateCoverage] at h
  | cons segment rest =>
      by_cases hc : segment.fromBlock ≤ first ∧ first < segment.toBlock
      · simp only [validateCoverage, if_pos hc] at h
        exact Nat.lt_of_lt_of_le hc.2 (validateTail_end segment.toBlock rest endBlock h)
      · simp [validateCoverage, hc] at h

private def planEntry (selection : Selection) (entry : Json) : Except String Plan := do
  let addresses ← tracked entry
  let transactionHashField ← extraFields entry
  let rawChunks ← asArray (← field entry "chunks")
  let mut chunks ← rawChunks.mapM (parseSegment false)
  if let some hot := optionalField entry "hotHead" then
    chunks := chunks.push (← parseSegment true hot)
  let first := firstReplayBlock selection
  let candidates := chunks.toList.mergeSort (fun a b => a.fromBlock ≤ b.fromBlock)
  let selected := candidates.filter (fun seg => seg.toBlock > first && seg.fromBlock ≤ selection.head)
  if !withinSegmentBudget selected.length then
    throw "Saga index selects too many chunks."
  let endBlock ← validateCoverage first selected
  let coverage := min selection.head (endBlock - 1)
  -- A fresh pool snapshot starts one block before registration. The first
  -- replay block is already clamped to registration above.
  if selection.registeredBlock > selection.lastSyncedBlock + 1 ||
      selection.lastSyncedBlock > selection.head || coverage < first then
    throw "Invalid pool snapshot or Saga coverage."
  return (⟨selection, first, coverage, addresses, transactionHashField,
    selected.toArray⟩ : Plan)

/-- Parse and select exactly one chain/pool stream. Any failure leaves the
    caller with no advertised coverage; it must use authenticated RPC fallback. -/
def planIndex (selection : Selection) (raw : ByteArray) : Except String Plan := do
  if raw.size > maxIndexBytes then throw "Saga index exceeds 2 MiB."
  let some text := String.fromUTF8? raw | throw invalid
  let json ← Json.parse text |>.mapError (fun _ => invalid)
  let version ← (← field json "version").getNat? |>.mapError (fun _ => invalid)
  if version != 1 && version != 2 then throw invalid
  if (← string json "compression") != "gzip" then throw invalid
  let entries ← (← field json "availableProtocols").getObj? |>.mapError (fun _ => invalid)
  let mut matched : Array Json := #[]
  for (_, entry) in entries.toList do
    if (← entryMatches selection entry) then matched := matched.push entry
  if matched.size != 1 then throw "No unique Saga pool stream."
  planEntry selection matched[0]!

/-- Bounds a consumer's inclusive request by already validated coverage. -/
def admitRange (history : ValidatedHistory) (fromBlock toBlock : Nat) :
    Except String (Array ValidatedEvent) :=
  if fromBlock < history.replayStart ∨ fromBlock > toBlock ∨
      toBlock > history.coverage then
    .error "Saga range exceeds validated history."
  else .ok (history.events.filter (fun event =>
    fromBlock ≤ event.blockNumber && event.blockNumber ≤ toBlock))

theorem accepted_range_is_within_coverage (history : ValidatedHistory)
    (fromBlock toBlock : Nat) (events : Array ValidatedEvent)
    (h : admitRange history fromBlock toBlock = .ok events) :
    history.replayStart ≤ fromBlock ∧ fromBlock ≤ toBlock ∧
      toBlock ≤ history.coverage := by
  by_cases blocked : fromBlock < history.replayStart ∨
      fromBlock > toBlock ∨ toBlock > history.coverage
  · simp [admitRange, blocked] at h
  · simp only [not_or] at blocked
    omega

private def decodeRecord (plan : Plan) (seg : Segment) (json : Json) :
    Except String ValidatedEvent := do
  let blockNumber ← quantity json "blockNumber"
  let logIndex ← quantity json "logIndex"
  if blockNumber < seg.fromBlock || blockNumber ≥ seg.toBlock then throw invalid
  let address ← checkedAddress json "contractAddress"
  if !plan.trackedAddresses.contains address then throw invalid
  let rawTopics ← asArray (← field json "topics")
  let topics ← rawTopics.mapM (fun item => do
    let raw ← item.getStr? |>.mapError (fun _ => invalid)
    fixedHex raw 32)
  let eventTopic ← string json "eventTopic"
  let some firstTopicJson := rawTopics[0]? | throw invalid
  let firstTopic ← firstTopicJson.getStr? |>.mapError (fun _ => invalid)
  if eventTopic != firstTopic then throw invalid
  let rawData ← string json "data"
  if !rawData.startsWith "0x" then throw invalid
  let data ← parseHexBytes rawData
  if data.size > 1024 * 1024 then throw invalid
  if plan.transactionHashField then
    let _ ← fixedHex (← string json "transactionHash") 32
  let log : Log := { address, topics, data }
  if topics[0]? == some depositTopic then
    let _ ← decodeDeposit log
    return { blockNumber, logIndex, log, isDeposit := true }
  if topics[0]? == some withdrawalTopic then
    let _ ← decodeWithdrawal log
    return { blockNumber, logIndex, log, isDeposit := false }
  throw "Unsupported Saga pool event."

private def parseChunk (plan : Plan) (seg : Segment) (compressed : ByteArray) :
    Except String (Array ValidatedEvent) := do
  if compressed.size > maxCompressedChunkBytes then
    throw "Saga chunk exceeds native decoder bound."
  let bytes ← if compressed[0]? == some 0x1f && compressed[1]? == some 0x8b then
    Tornado.Compression.Gzip.decompress compressed maxDecodedChunkBytes
  else .ok compressed
  if bytes.size > maxDecodedChunkBytes then throw "Saga decoded chunk exceeds native bound."
  if sha256Hex bytes != seg.digest then throw "Saga chunk checksum mismatch."
  let some text := String.fromUTF8? bytes | throw invalid
  let mut previous : Option (Nat × Nat) := none
  let mut selected := #[]
  let mut count := 0
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    count := count + 1
    if count > maxEventsPerChunk then throw "Saga chunk has too many events."
    let json ← Json.parse line |>.mapError (fun _ => invalid)
    let event ← decodeRecord plan seg json
    if let some (block, log) := previous then
      if event.blockNumber < block ||
          (event.blockNumber == block && event.logIndex ≤ log) then
        throw "Saga events are out of order."
    previous := some (event.blockNumber, event.logIndex)
    if event.log.address == plan.selection.pool &&
        event.blockNumber ≥ plan.replayStart && event.blockNumber ≤ plan.coverage then
      selected := selected.push event
  return selected

/-- Validate all selected gzip chunks before exposing any pool history. The
    chunk array must match `plan.segments` exactly in manifest order. -/
def validateChunks (plan : Plan) (chunks : Array ByteArray) :
    Except String ValidatedHistory := do
  if chunks.size != plan.segments.size then throw "Saga chunk count mismatch."
  if !withinSegmentBudget chunks.size || !withinChunkByteBudget chunks then
    throw "Saga chunk resource budget exceeded."
  let mut events := #[]
  for i in [0:plan.segments.size] do
    let parsed ← parseChunk plan plan.segments[i]! chunks[i]!
    if events.size + parsed.size > maxSelectedEvents then
      throw "Saga event resource budget exceeded."
    events := events ++ parsed
  return { replayStart := plan.replayStart, coverage := plan.coverage, events }

/-- A partial Saga stream needs an RPC tail. After the SDK/importer has
    consumed Saga and RPC events, re-check the exact selected pool cursor. -/
def assertPoolFreshness (selection : Selection) (state : SyncedPool) :
    Except String Unit :=
  if state.chainId == selection.chainId && state.pool == selection.pool &&
      state.lastSyncedBlock ≥ selection.head then .ok ()
  else .error "Selected pool history is incomplete or belongs to another chain/pool."

theorem accepted_freshness_covers_head (selection : Selection)
    (state : SyncedPool)
    (h : assertPoolFreshness selection state = .ok ()) :
    state.chainId = selection.chainId ∧ state.pool = selection.pool ∧
      selection.head ≤ state.lastSyncedBlock := by
  unfold assertPoolFreshness at h
  by_cases hc : state.chainId = selection.chainId
  · by_cases hp : state.pool = selection.pool
    · by_cases hh : selection.head ≤ state.lastSyncedBlock
      · exact ⟨hc, hp, hh⟩
      · simp [hc, hp, hh] at h
    · simp [hc, hp] at h
  · simp [hc] at h

end Tornado.Protocol.SagaHistory

#print axioms Tornado.Protocol.SagaHistory.replay_never_before_registration
#print axioms Tornado.Protocol.SagaHistory.cursor_before_registration_replay
#print axioms Tornado.Protocol.SagaHistory.validateTail_sound
#print axioms Tornado.Protocol.SagaHistory.validateTail_end
#print axioms Tornado.Protocol.SagaHistory.validate_coverage_sound
#print axioms Tornado.Protocol.SagaHistory.validate_coverage_end
#print axioms Tornado.Protocol.SagaHistory.accepted_range_is_within_coverage
#print axioms Tornado.Protocol.SagaHistory.accepted_freshness_covers_head
