import Lean
import Tornado.Policy
import Tornado.Policy.Batch
import Tornado.Runtime.ProtectedIO

/-!
Append-only, per-attempt intent records. `createPrivate` durably creates each
record before this module acknowledges it. The caller must append `expose` and
`send` before the corresponding network effect. This module does not perform
those effects or authenticate chain evidence.
-/

namespace Tornado.Runtime.AttemptJournal

open Lean

inductive Kind where
  | direct | batch
  deriving Repr, BEq, DecidableEq

inductive Event where
  | prepare (hash : String) (nullifiers : List String)
  | sign (hash : String)
  | reserve (nullifier : String)
  | expose
  | send
  | unknown
  | confirm (hash receiptRef : String) (receiptSuccess entryPointMatches
      withdrawalMatches : Bool) (matchedNullifiers : List String)
  deriving Repr

structure Record where
  attemptId : String
  kind : Kind
  seq : Nat
  event : Event
  deriving Repr

structure State where
  attemptId : String
  kind : Kind
  nextSeq : Nat := 0
  selected : List String := []
  direct : Tornado.Policy.Attempt := {}
  batch : Tornado.Policy.Batch.Attempt := {}
  deriving Repr

/-- At most 18 records are needed for a 12-note batch, including an optional
    unknown and subsequent confirmation. The cap is 20 records; a longer
    history is rejected, never truncated. -/
def maxRecords : Nat := 20

private def invalid : String := "Invalid or inconsistent attempt journal"

private def lowerHex (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

private def validId (id : String) : Bool :=
  id.length == 32 && id.toList.all lowerHex

private def validDigest (value : String) : Bool :=
  value.length == 66 && value.startsWith "0x" &&
    (value.toList.drop 2).all lowerHex

private def validSelection (kind : Kind) (notes : List String) : Bool :=
  notes.all validDigest &&
    (if kind == .direct then notes.length == 1
     else Tornado.Policy.Batch.validSelection notes)

private def kindText : Kind → String
  | .direct => "direct"
  | .batch => "batch"

private def parseKind (raw : String) : Except String Kind :=
  match raw with
  | "direct" => .ok .direct
  | "batch" => .ok .batch
  | _ => .error invalid

private def eventJson : Event → Json
  | .prepare hash notes => Json.mkObj [
      ("tag", toJson ("prepare" : String)), ("hash", toJson hash),
      ("nullifiers", toJson notes)]
  | .sign hash => Json.mkObj [
      ("tag", toJson ("sign" : String)), ("hash", toJson hash)]
  | .reserve note => Json.mkObj [
      ("tag", toJson ("reserve" : String)), ("nullifier", toJson note)]
  | .expose => Json.mkObj [("tag", toJson ("expose" : String))]
  | .send => Json.mkObj [("tag", toJson ("send" : String))]
  | .unknown => Json.mkObj [("tag", toJson ("unknown" : String))]
  | .confirm hash ref success entry withdrawal matched => Json.mkObj [
      ("tag", toJson ("confirm" : String)),
      ("hash", toJson hash), ("receiptRef", toJson ref),
      ("receiptSuccess", toJson success),
      ("entryPointMatches", toJson entry),
      ("withdrawalMatches", toJson withdrawal),
      ("matchedNullifiers", toJson matched)]

/-- Canonical UTF-8 bytes are the on-disk format. Re-encoding on read rejects
    unknown fields, duplicate JSON keys, whitespace and alternate spellings. -/
def encode (record : Record) : String :=
  (Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("attemptId", toJson record.attemptId),
    ("kind", toJson (kindText record.kind)),
    ("seq", toJson record.seq),
    ("event", eventJson record.event)]).compress

private def strField (json : Json) (name : String) : Except String String := do
  (← json.getObjVal? name).getStr?

private def boolField (json : Json) (name : String) : Except String Bool := do
  (← json.getObjVal? name).getBool?

private def stringListField (json : Json) (name : String) : Except String (List String) := do
  let values ← (← json.getObjVal? name).getArr?
  values.toList.mapM Json.getStr?

private def parseEvent (json : Json) : Except String Event := do
  match ← strField json "tag" with
  | "prepare" =>
      let hash ← strField json "hash"
      let notes ← stringListField json "nullifiers"
      return .prepare hash notes
  | "sign" => return .sign (← strField json "hash")
  | "reserve" => return .reserve (← strField json "nullifier")
  | "expose" => return .expose
  | "send" => return .send
  | "unknown" => return .unknown
  | "confirm" =>
      let hash ← strField json "hash"
      let ref ← strField json "receiptRef"
      let success ← boolField json "receiptSuccess"
      let entry ← boolField json "entryPointMatches"
      let withdrawal ← boolField json "withdrawalMatches"
      let matched ← stringListField json "matchedNullifiers"
      return .confirm hash ref success entry withdrawal matched
  | _ => throw invalid

/-- Strictly decode one canonical record. -/
def decode (raw : String) : Except String Record := do
  let json ← Json.parse raw
  let version ← (← json.getObjVal? "version").getNat?
  if version != 1 then throw invalid
  let record : Record := {
    attemptId := ← strField json "attemptId"
    kind := ← parseKind (← strField json "kind")
    seq := ← (← json.getObjVal? "seq").getNat?
    event := ← parseEvent (← json.getObjVal? "event")
  }
  if encode record != raw then throw invalid
  return record

private def advance (state : State) (event : Event) : Except String State := do
  if state.nextSeq >= maxRecords then throw invalid
  match event with
  | .prepare hash notes =>
      if !validDigest hash || !validSelection state.kind notes then throw invalid
      if state.kind == .direct then
        let next ← Tornado.Policy.stepAttempt state.direct (.approve hash)
        return { state with direct := next, selected := notes, nextSeq := state.nextSeq + 1 }
      else
        let next ← Tornado.Policy.Batch.step state.batch (.prepare notes hash)
        return { state with batch := next, selected := notes, nextSeq := state.nextSeq + 1 }
  | .sign hash =>
      if !validDigest hash then throw invalid
      if state.kind == .direct then
        let next ← Tornado.Policy.stepAttempt state.direct (.sign hash)
        return { state with direct := next, nextSeq := state.nextSeq + 1 }
      else
        let next ← Tornado.Policy.Batch.step state.batch (.sign hash)
        return { state with batch := next, nextSeq := state.nextSeq + 1 }
  | .reserve note =>
      if !validDigest note || !state.selected.contains note then throw invalid
      if state.kind == .direct then
        let next ← Tornado.Policy.stepAttempt state.direct .reserve
        return { state with direct := next, nextSeq := state.nextSeq + 1 }
      else
        let next ← Tornado.Policy.Batch.step state.batch (.reserveNote note)
        return { state with batch := next, nextSeq := state.nextSeq + 1 }
  | .expose =>
      if state.kind == .direct then
        let next ← Tornado.Policy.stepAttempt state.direct .expose
        return { state with direct := next, nextSeq := state.nextSeq + 1 }
      else
        let next ← Tornado.Policy.Batch.step state.batch .expose
        return { state with batch := next, nextSeq := state.nextSeq + 1 }
  | .send =>
      if state.kind == .direct then
        let next ← Tornado.Policy.stepAttempt state.direct .send
        return { state with direct := next, nextSeq := state.nextSeq + 1 }
      else
        let next ← Tornado.Policy.Batch.step state.batch .send
        return { state with batch := next, nextSeq := state.nextSeq + 1 }
  | .unknown =>
      if state.kind == .direct then
        let next ← Tornado.Policy.stepAttempt state.direct .markUnknown
        return { state with direct := next, nextSeq := state.nextSeq + 1 }
      else
        let next ← Tornado.Policy.Batch.step state.batch .markUnknown
        return { state with batch := next, nextSeq := state.nextSeq + 1 }
  | .confirm hash ref success entry withdrawal matched =>
      if !validDigest hash || !validDigest ref ||
          !matched.all validDigest || !success || !entry || !withdrawal then
        throw invalid
      if state.kind == .direct then
        if state.direct.signedHash != some hash || matched != state.selected then
          throw invalid
        let next ← Tornado.Policy.stepAttempt state.direct (.confirm {
          receiptSuccess := success
          entryPointEventMatches := entry
          withdrawalEventMatches := withdrawal })
        return { state with direct := next, nextSeq := state.nextSeq + 1 }
      else
        let next ← Tornado.Policy.Batch.step state.batch (.confirm {
          receiptSuccess := success
          entryPointEventMatches := entry
          userOpHash := hash
          matchedNullifiers := matched })
        return { state with batch := next, nextSeq := state.nextSeq + 1 }

/-- The pure replay step used by `load` after a protected read and canonical
    decode. Its identity/sequence check is part of the executable journal
    parser, so proofs over this function constrain the actual replay path. -/
def replayRecord (state : State) (record : Record) : Except String State :=
  if record.attemptId = state.attemptId ∧ record.kind = state.kind ∧
      record.seq = state.nextSeq then
    advance state record.event
  else .error invalid

private def fromExcept (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def checkArguments (directory id : String) : IO Unit := do
  if directory.isEmpty || !(System.FilePath.mk directory).isAbsolute ||
      directory.endsWith "/" || !validId id then
    throw <| IO.userError invalid

/-- File names are scoped by a caller-supplied random 128-bit attempt ID.
    The create operation uses O_EXCL, so concurrent writers cannot replace a
    slot. -/
def fileName (id : String) (seq : Nat) : String := s!"{id}.{seq}.journal"

private def filePath (directory id : String) (seq : Nat) : String :=
  directory ++ "/" ++ fileName id seq

/-- Reconstruct all state from disk. Empty histories, malformed names, gaps,
    unsafe files and invalid policy transitions are errors. Directory listing
    is only an index; each record is opened through `readPrivate`. -/
def load (directory id : String) (kind : Kind) : IO State := do
  checkArguments directory id
  let entries ← System.FilePath.readDir (System.FilePath.mk directory)
  let namePrefix := id ++ "."
  let names := (entries.toList.map (·.fileName)).filter (·.startsWith namePrefix)
  if names.isEmpty || names.length > maxRecords then
    throw <| IO.userError invalid
  for seq in [0:names.length] do
    if !names.contains (fileName id seq) then
      throw <| IO.userError invalid
  let mut state : State := { attemptId := id, kind := kind }
  for seq in [0:names.length] do
    let bytes ← Tornado.Runtime.ProtectedIO.readPrivate (filePath directory id seq)
    let some raw := String.fromUTF8? bytes
      | throw <| IO.userError invalid
    let record ← fromExcept (decode raw)
    state ← fromExcept (replayRecord state record)
  return state

/-- Start a unique attempt with a durable preparation record. A failed or
    ambiguous create returns an error; callers must reload before deciding
    what happened. -/
def start (directory id : String) (kind : Kind) (hash : String)
    (nullifiers : List String) : IO State := do
  checkArguments directory id
  let initial : State := { attemptId := id, kind := kind }
  let event := Event.prepare hash nullifiers
  let _ ← fromExcept (advance initial event)
  let record : Record := { attemptId := id, kind := kind, seq := 0, event := event }
  Tornado.Runtime.ProtectedIO.createPrivate (filePath directory id 0) (encode record).toUTF8
  let state ← load directory id kind
  if state.nextSeq != 1 then throw <| IO.userError invalid
  return state

private def appendChecked (directory id : String) (kind : Kind)
    (event : Event) : IO State := do
  let state ← load directory id kind
  let _ ← fromExcept (advance state event)
  let record : Record := {
    attemptId := id, kind := kind, seq := state.nextSeq, event := event }
  Tornado.Runtime.ProtectedIO.createPrivate
    (filePath directory id state.nextSeq) (encode record).toUTF8
  let reloaded ← load directory id kind
  if reloaded.nextSeq != state.nextSeq + 1 then
    throw <| IO.userError invalid
  return reloaded

/-- Validate against freshly reconstructed state, create the next immutable
    record, then reload. Never return an advanced in-memory state when the
    durable write fails. A standalone exposure intent is terminal for sending:
    a restart cannot distinguish whether a proof-bearing RPC relayed it. -/
def append (directory id : String) (kind : Kind) (event : Event) : IO State :=
  match event with
  | .send => throw <| IO.userError "Send intent must be armed before any network exposure"
  | _ => appendChecked directory id kind event

/-- Durably append exposure and the one permitted send intent in one local
    operation, with no network effect between writes. If the process crashes
    after only the exposure file, replay cannot arm a later send. A successful
    return permits the caller to perform at most one send; any ambiguous result
    must be treated as unknown and reconciled, never retried. -/
def armSubmission (directory id : String) (kind : Kind) : IO State := do
  let exposed ← appendChecked directory id kind .expose
  let submitted ← appendChecked directory id kind .send
  if submitted.nextSeq != exposed.nextSeq + 1 then
    throw <| IO.userError invalid
  return submitted

end Tornado.Runtime.AttemptJournal

namespace Tornado.Runtime.AttemptJournal

/-- Successful pure preparation binds the selected nullifier list to the
    resulting journal state and only accepts the strict digest grammar. -/
theorem advance_prepare_binds_selection (before after : State)
    (hash : String) (notes : List String)
    (accepted : advance before (.prepare hash notes) = .ok after) :
    validDigest hash = true ∧ validSelection before.kind notes = true ∧
      after.selected = notes := by
  by_cases hb : before.nextSeq ≥ maxRecords
  · simp [advance, hb] at accepted
    change Except.error invalid = Except.ok after at accepted
    cases accepted
  · cases hh : validDigest hash with
    | false =>
        simp [advance, hb, hh] at accepted
        change Except.error invalid = Except.ok after at accepted
        cases accepted
    | true =>
        cases hs : validSelection before.kind notes with
        | false =>
            simp [advance, hb, hh, hs] at accepted
            change Except.error invalid = Except.ok after at accepted
            cases accepted
        | true =>
            cases hk : before.kind with
            | direct =>
                have hSel : validSelection Kind.direct notes = true := by
                  simpa [hk] using hs
                cases hp : Tornado.Policy.stepAttempt before.direct (.approve hash) with
                | error e =>
                    simp [advance, hb, hh, hSel, hk, hp] at accepted
                    change Except.error e = Except.ok after at accepted
                    cases accepted
                | ok next =>
                    simp [advance, hb, hh, hSel, hk, hp] at accepted
                    dsimp [Functor.map, Except.map] at accepted
                    cases accepted
                    exact ⟨rfl, rfl, rfl⟩

            | batch =>
                have hSel : validSelection Kind.batch notes = true := by
                  simpa [hk] using hs
                cases hp : Tornado.Policy.Batch.step before.batch (.prepare notes hash) with
                | error e =>
                    simp [advance, hb, hh, hSel, hk, hp] at accepted
                    change Except.error e = Except.ok after at accepted
                    cases accepted
                | ok next =>
                    simp [advance, hb, hh, hSel, hk, hp] at accepted
                    dsimp [Functor.map, Except.map] at accepted
                    cases accepted
                    exact ⟨rfl, rfl, rfl⟩


/-- Replay only accepts a reservation for a canonical nullifier that is in
    the prepared selection. -/
theorem advance_reserve_selected (before after : State) (note : String)
    (accepted : advance before (.reserve note) = .ok after) :
    validDigest note = true ∧ before.selected.contains note = true := by
  by_cases hb : before.nextSeq ≥ maxRecords
  · simp [advance, hb] at accepted
    change Except.error invalid = Except.ok after at accepted
    cases accepted
  · cases hd : validDigest note with
    | false =>
        simp [advance, hb, hd] at accepted
        change Except.error invalid = Except.ok after at accepted
        cases accepted
    | true =>
        cases hc : before.selected.contains note with
        | false =>
            have hNoMem : note ∉ before.selected := by
              intro hm
              have contradiction : before.selected.contains note = true :=
                List.contains_iff_mem.mpr hm
              rw [hc] at contradiction
              cases contradiction
            simp [advance, hb, hd, hNoMem] at accepted
            change Except.error invalid = Except.ok after at accepted
            cases accepted
        | true => exact ⟨rfl, rfl⟩

/-- Accepted direct send replay is exactly a policy-approved send of the
    previously reconstructed direct state. This is a pure replay fact only. -/
theorem advance_direct_send_refines_policy (before after : State)
    (hk : before.kind = .direct)
    (accepted : advance before .send = .ok after) :
    ∃ next, Tornado.Policy.stepAttempt before.direct .send = .ok next ∧
      after = { before with direct := next, nextSeq := before.nextSeq + 1 } := by
  have kindTrue : (Kind.direct == Kind.direct) = true := by decide
  by_cases hb : before.nextSeq ≥ maxRecords
  · simp [advance, hk, hb, kindTrue] at accepted
    change Except.error invalid = Except.ok after at accepted
    cases accepted
  · cases hp : Tornado.Policy.stepAttempt before.direct .send with
    | error e =>
        simp [advance, hk, hb, kindTrue, hp] at accepted
        change Except.error e = Except.ok after at accepted
        cases accepted
    | ok next =>
        simp [advance, hk, hb, kindTrue, hp] at accepted
        dsimp [Functor.map, Except.map] at accepted
        cases accepted
        exact ⟨next, rfl, by simp [hk]⟩

/-- A replayed direct send cannot pass unless the prior state was exposed,
    bound to the same nonempty signed/reserved hash, and unused. -/
theorem advance_direct_send_requires_exposed (before after : State)
    (hk : before.kind = .direct)
    (accepted : advance before .send = .ok after) :
    before.direct.phase = .exposed ∧
    before.direct.reservedHash = before.direct.signedHash ∧
    before.direct.reservedHash.isSome = true ∧
    before.direct.sends = 0 := by
  obtain ⟨next, policy, _⟩ :=
    advance_direct_send_refines_policy before after hk accepted
  cases hp : before.direct.phase <;> simp [Tornado.Policy.stepAttempt, hp] at policy
  by_cases hcond :
      (before.direct.reservedHash = before.direct.signedHash ∧
        before.direct.reservedHash.isSome = true) ∧ before.direct.sends = 0
  · exact ⟨rfl, hcond.1.1, hcond.1.2, hcond.2⟩
  · simp [hcond] at policy

/-- Replay of an accepted direct send consumes the one send slot. -/
theorem advance_direct_send_consumes_slot (before after : State)
    (hk : before.kind = .direct)
    (accepted : advance before .send = .ok after) :
    after.direct.phase = .submitted ∧ after.direct.sends = 1 := by
  obtain ⟨next, policy, final⟩ :=
    advance_direct_send_refines_policy before after hk accepted
  obtain ⟨phase, hashes, nonempty, sends⟩ :=
    advance_direct_send_requires_exposed before after hk accepted
  have signedSome : before.direct.signedHash.isSome = true := by
    simpa [hashes] using nonempty
  simp [Tornado.Policy.stepAttempt, phase, hashes, signedSome, sends] at policy
  subst after
  simp [← policy]

/-- Once replay has accepted the direct send event, it rejects another send
    event in the same journal state. -/
theorem advance_direct_send_no_repeat (before after later : State)
    (hk : before.kind = .direct)
    (first : advance before .send = .ok after)
    (second : advance after .send = .ok later) : False := by
  obtain ⟨next, _, final⟩ :=
    advance_direct_send_refines_policy before after hk first
  have afterKind : after.kind = .direct := by simp [final, hk]
  have consumed := advance_direct_send_consumes_slot before after hk first
  have required := advance_direct_send_requires_exposed after later afterKind second
  rw [consumed.1] at required
  cases required.1

/-- Accepted batch send replay is exactly an approved batch policy send. -/
theorem advance_batch_send_refines_policy (before after : State)
    (hk : before.kind = .batch)
    (accepted : advance before .send = .ok after) :
    ∃ next, Tornado.Policy.Batch.step before.batch .send = .ok next ∧
      after = { before with batch := next, nextSeq := before.nextSeq + 1 } := by
  have kindFalse : (Kind.batch == Kind.direct) = false := by decide
  by_cases hb : before.nextSeq ≥ maxRecords
  · simp [advance, hk, hb, kindFalse] at accepted
    change Except.error invalid = Except.ok after at accepted
    cases accepted
  · cases hp : Tornado.Policy.Batch.step before.batch .send with
    | error e =>
        simp [advance, hk, hb, kindFalse, hp] at accepted
        change Except.error e = Except.ok after at accepted
        cases accepted
    | ok next =>
        simp [advance, hk, hb, kindFalse, hp] at accepted
        dsimp [Functor.map, Except.map] at accepted
        cases accepted
        exact ⟨next, rfl, by simp [hk]⟩

/-- A replayed batch send requires every selected note reserved and a
    matching nonempty reviewed/signed hash in the prior policy state. -/
theorem advance_batch_send_requires_reserved (before after : State)
    (hk : before.kind = .batch)
    (accepted : advance before .send = .ok after) :
    (before.batch.phase == .exposed) = true ∧
    Tornado.Policy.Batch.allReserved before.batch = true ∧
    before.batch.reviewedHash = before.batch.signedHash ∧
    before.batch.signedHash.isSome = true ∧
    before.batch.sends = 0 := by
  obtain ⟨next, policy, _⟩ :=
    advance_batch_send_refines_policy before after hk accepted
  have hcond :
      (before.batch.phase == Tornado.Policy.Batch.Phase.exposed &&
        Tornado.Policy.Batch.allReserved before.batch &&
        (before.batch.reviewedHash == before.batch.signedHash) &&
        before.batch.signedHash.isSome && before.batch.sends == 0) = true := by
    cases hg : (before.batch.phase == Tornado.Policy.Batch.Phase.exposed &&
        Tornado.Policy.Batch.allReserved before.batch &&
        (before.batch.reviewedHash == before.batch.signedHash) &&
        before.batch.signedHash.isSome && before.batch.sends == 0) with
    | false => simp [Tornado.Policy.Batch.step, hg] at policy
    | true => rfl
  simp only [Bool.and_eq_true, beq_iff_eq] at hcond
  exact ⟨hcond.1.1.1.1, hcond.1.1.1.2, hcond.1.1.2,
    hcond.1.2, hcond.2⟩

/-- Replay of an accepted batch send consumes the one send slot. -/
theorem advance_batch_send_consumes_slot (before after : State)
    (hk : before.kind = .batch)
    (accepted : advance before .send = .ok after) :
    after.batch.phase = .submitted ∧ after.batch.sends = 1 := by
  obtain ⟨next, policy, final⟩ :=
    advance_batch_send_refines_policy before after hk accepted
  obtain ⟨phase, reserved, hashes, nonempty, sends⟩ :=
    advance_batch_send_requires_reserved before after hk accepted
  have gate :
      (before.batch.phase == Tornado.Policy.Batch.Phase.exposed &&
        Tornado.Policy.Batch.allReserved before.batch &&
        (before.batch.reviewedHash == before.batch.signedHash) &&
        before.batch.signedHash.isSome && before.batch.sends == 0) = true := by
    simp [phase, reserved, hashes, nonempty, sends]
  simp [Tornado.Policy.Batch.step, gate] at policy
  subst after
  simp [← policy]

/-- Once replay has accepted the batch send event, it rejects a second send. -/
theorem advance_batch_send_no_repeat (before after later : State)
    (hk : before.kind = .batch)
    (first : advance before .send = .ok after)
    (second : advance after .send = .ok later) : False := by
  obtain ⟨next, _, final⟩ :=
    advance_batch_send_refines_policy before after hk first
  have afterKind : after.kind = .batch := by simp [final, hk]
  have consumed := advance_batch_send_consumes_slot before after hk first
  have required := advance_batch_send_requires_reserved after later afterKind second
  have impossible : (Tornado.Policy.Batch.Phase.submitted ==
      Tornado.Policy.Batch.Phase.exposed) = false := by decide
  rw [consumed.1, impossible] at required
  cases required.1

end Tornado.Runtime.AttemptJournal

#print axioms Tornado.Runtime.AttemptJournal.advance_direct_send_refines_policy
#print axioms Tornado.Runtime.AttemptJournal.advance_direct_send_requires_exposed
#print axioms Tornado.Runtime.AttemptJournal.advance_direct_send_consumes_slot
#print axioms Tornado.Runtime.AttemptJournal.advance_direct_send_no_repeat
#print axioms Tornado.Runtime.AttemptJournal.advance_batch_send_refines_policy
#print axioms Tornado.Runtime.AttemptJournal.advance_batch_send_requires_reserved
#print axioms Tornado.Runtime.AttemptJournal.advance_batch_send_consumes_slot
#print axioms Tornado.Runtime.AttemptJournal.advance_batch_send_no_repeat
#print axioms Tornado.Runtime.AttemptJournal.advance_prepare_binds_selection
#print axioms Tornado.Runtime.AttemptJournal.advance_reserve_selected
