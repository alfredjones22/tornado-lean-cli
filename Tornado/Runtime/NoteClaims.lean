import Lean
import Tornado.Runtime.AttemptJournal
import Tornado.Runtime.ProtectedIO

/-!
Permanent, exclusive per-nullifier claims for one local CLI instance. A claim
is created and fsynced before its attempt journal is started. Claims are never
automatically released, because a missing or ambiguous receipt is not evidence
that the note can be safely reused. The two-file/multi-file sequence is not an
atomic transaction; an interrupted batch may leave orphan claims.
-/

namespace Tornado.Runtime.NoteClaims

open Lean
open Tornado.Runtime.AttemptJournal

private def invalid : String := "Invalid or inconsistent note claim"

private def lowerHex (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

def validAttemptId (id : String) : Bool :=
  id.length == 32 && id.toList.all lowerHex

def validDigest (value : String) : Bool :=
  value.length == 66 && value.startsWith "0x" &&
    (value.toList.drop 2).all lowerHex

def validSelection (kind : Kind) (notes : List String) : Bool :=
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

structure Claim where
  attemptId : String
  kind : Kind
  reviewedHash : String
  nullifier : String
  selected : List String
  deriving Repr, BEq

/-- All records for one attempt carry its whole ordered selection and reviewed
    operation hash. Re-encoding rejects alternate JSON spellings on read. -/
def encode (claim : Claim) : String :=
  (Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("attemptId", toJson claim.attemptId),
    ("kind", toJson (kindText claim.kind)),
    ("reviewedHash", toJson claim.reviewedHash),
    ("nullifier", toJson claim.nullifier),
    ("selected", toJson claim.selected)]).compress

private def strField (json : Json) (name : String) : Except String String := do
  (← json.getObjVal? name).getStr?

/-- Strict canonical claim decoder; no missing, extra, or duplicate fields. -/
def decode (raw : String) : Except String Claim := do
  let json ← Json.parse raw
  let version ← (← json.getObjVal? "version").getNat?
  if version != 1 then throw invalid
  let selected ← (← json.getObjVal? "selected").getArr?
  let claim : Claim := {
    attemptId := ← strField json "attemptId"
    kind := ← parseKind (← strField json "kind")
    reviewedHash := ← strField json "reviewedHash"
    nullifier := ← strField json "nullifier"
    selected := ← selected.toList.mapM Json.getStr? }
  if encode claim != raw || !validAttemptId claim.attemptId ||
      !validDigest claim.reviewedHash || !validDigest claim.nullifier ||
      !validSelection claim.kind claim.selected ||
      !claim.selected.contains claim.nullifier then
    throw invalid
  return claim

private def fromExcept (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def checkRoot (root : String) : IO Unit := do
  if root.isEmpty || !(System.FilePath.mk root).isAbsolute || root.endsWith "/" then
    throw <| IO.userError invalid

private def checkInput (root id hash : String) (kind : Kind)
    (notes : List String) : IO Unit := do
  checkRoot root
  if !validAttemptId id || !validDigest hash || !validSelection kind notes then
    throw <| IO.userError invalid

private def claimsDirectory (root : String) : String := root ++ "/claims"
private def attemptsDirectory (root : String) : String := root ++ "/attempts"

/-- The claim name reveals the nullifier hash, so both child directories must
    be unreadable and untraversable to other local principals. -/
private def checkDirectories (root : String) : IO Unit := do
  Tornado.Runtime.ProtectedIO.checkPrivateDirectory (claimsDirectory root)
  Tornado.Runtime.ProtectedIO.checkPrivateDirectory (attemptsDirectory root)

/-- The filename intentionally omits chain and pool. Reusing a nullifier on
    another pool or chain is conservatively blocked by this local instance. -/
def fileName (nullifier : String) : String :=
  String.ofList (nullifier.toList.drop 2) ++ ".claim"

private def filePath (root nullifier : String) : String :=
  claimsDirectory root ++ "/" ++ fileName nullifier

/-- Read and validate one claim through the protected OS binding. -/
def readClaim (root nullifier : String) : IO Claim := do
  checkRoot root
  if !validDigest nullifier then throw <| IO.userError invalid
  checkDirectories root
  let bytes ← Tornado.Runtime.ProtectedIO.readPrivate (filePath root nullifier)
  let some raw := String.fromUTF8? bytes
    | throw <| IO.userError invalid
  let claim ← fromExcept (decode raw)
  if claim.nullifier != nullifier then throw <| IO.userError invalid
  return claim

/-- Create every permanent note claim before starting the journal. If any
    write fails, stop; never reinterpret a same-attempt EEXIST as success.
    Partial claims are left in place and require manual investigation. -/
def claimAll (root id : String) (kind : Kind) (hash : String)
    (notes : List String) : IO Unit := do
  checkInput root id hash kind notes
  checkDirectories root
  for note in notes do
    let claim : Claim := ⟨id, kind, hash, note, notes⟩
    Tornado.Runtime.ProtectedIO.createPrivate
      (filePath root note) (encode claim).toUTF8

/-- Start a journal only after all selected nullifiers have durable exclusive
    claims. A failed journal start still leaves claims locked. -/
def startClaimed (root id : String) (kind : Kind) (hash : String)
    (notes : List String) : IO State := do
  claimAll root id kind hash notes
  let state ← Tornado.Runtime.AttemptJournal.start
    (attemptsDirectory root) id kind hash notes
  if state.selected != notes then throw <| IO.userError invalid
  return state

/-- Reconstruct the journal and match *every* selected nullifier's immutable
    claim to its attempt ID, kind, reviewed hash, and entire ordered selection.
    This is a precondition for any state advance through this wrapper. -/
def loadClaimed (root id : String) (kind : Kind) : IO State := do
  checkRoot root
  if !validAttemptId id then throw <| IO.userError invalid
  checkDirectories root
  let state ← Tornado.Runtime.AttemptJournal.load (attemptsDirectory root) id kind
  let some hash := (match kind with
      | .direct => state.direct.reviewedHash
      | .batch => state.batch.reviewedHash)
    | throw <| IO.userError invalid
  if !validSelection kind state.selected then throw <| IO.userError invalid
  for note in state.selected do
    let actual ← readClaim root note
    let expected : Claim := ⟨id, kind, hash, note, state.selected⟩
    if actual != expected then throw <| IO.userError invalid
  return state

/-- Wrap journal transitions so every selected claim is checked first. The
    journal's own transition and exclusive-record logic remain authoritative. -/
def appendClaimed (root id : String) (kind : Kind) (event : Event) : IO State := do
  let _ ← loadClaimed root id kind
  Tornado.Runtime.AttemptJournal.append (attemptsDirectory root) id kind event

/-- Check claims, then arm the one irreversible exposure/send pair. The caller
    must perform no network effect before this returns successfully. -/
def armClaimedSubmission (root id : String) (kind : Kind) : IO State := do
  let _ ← loadClaimed root id kind
  Tornado.Runtime.AttemptJournal.armSubmission (attemptsDirectory root) id kind

end Tornado.Runtime.NoteClaims

namespace Tornado.Runtime.NoteClaims

/-- Within the fixed two-character prefix namespace, distinct nullifier
    strings cannot select the same claim filename. This is a property of
    the pure filename mapping, not of OS exclusive-create behavior. -/
theorem fileName_injective_of_same_prefix (a b : String)
    (samePrefix : a.toList.take 2 = b.toList.take 2)
    (names : fileName a = fileName b) : a = b := by
  have tails : a.toList.drop 2 = b.toList.drop 2 := by
    have strings : String.ofList (a.toList.drop 2) =
        String.ofList (b.toList.drop 2) := by
      exact (String.append_left_inj ".claim").mp names
    exact String.ofList_inj.mp strings
  have lists : a.toList = b.toList := by
    calc
      a.toList = a.toList.take 2 ++ a.toList.drop 2 :=
        (List.take_append_drop 2 a.toList).symm
      _ = b.toList.take 2 ++ b.toList.drop 2 := by rw [samePrefix, tails]
      _ = b.toList := List.take_append_drop 2 b.toList
  exact String.toList_inj.mp lists

/-- This directly rules out two distinct claim identifiers with the same
    prefix resolving to the same path. The OS exclusivity guarantee is a
    separate requirement of the protected file binding. -/
theorem fileName_ne_of_ne_same_prefix (a b : String)
    (samePrefix : a.toList.take 2 = b.toList.take 2)
    (distinct : a ≠ b) : fileName a ≠ fileName b := by
  intro names
  exact distinct (fileName_injective_of_same_prefix a b samePrefix names)

end Tornado.Runtime.NoteClaims

#print axioms Tornado.Runtime.NoteClaims.fileName_injective_of_same_prefix
#print axioms Tornado.Runtime.NoteClaims.fileName_ne_of_ne_same_prefix
