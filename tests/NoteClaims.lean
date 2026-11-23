import Tornado.Runtime.NoteClaims

open Tornado.Runtime.NoteClaims

private def repeated (char : Char) (count : Nat) : String :=
  String.ofList (List.replicate count char)

private def ensure (condition : Bool) (description : String) : IO Unit :=
  unless condition do throw <| IO.userError description

private def failed (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def exercise (root : String) : IO Unit := do
  let hash := "0x" ++ repeated 'a' 64
  let noteA := "0x" ++ repeated '1' 64
  let noteB := "0x" ++ repeated '2' 64
  let noteC := "0x" ++ repeated '3' 64
  let noteD := "0x" ++ repeated '4' 64
  let noteE := "0x" ++ repeated '5' 64
  let noteF := "0x" ++ repeated '6' 64
  let noteG := "0x" ++ repeated '7' 64
  let noteH := "0x" ++ repeated '8' 64
  let noteI := "0x" ++ repeated '9' 64
  let directId := repeated 'b' 32
  let secondId := repeated 'c' 32
  let batchId := repeated 'd' 32
  let partialId := repeated 'e' 32
  let conflictId := repeated 'f' 32
  let journalOnlyId := repeated '0' 32
  let mismatchId := repeated 'a' 32

  let sample : Claim := ⟨directId, .direct, hash, noteA, [noteA]⟩
  ensure ((decode (encode sample)).isOk) "Canonical claim did not roundtrip"
  ensure (!(decode (encode sample ++ "\n")).isOk)
    "Noncanonical claim was accepted"
  ensure (!(decode (encode { sample with selected := [noteB] })).isOk)
    "Claim whose nullifier is not selected was accepted"
  ensure (!(decode (encode { sample with attemptId := "not-id" })).isOk)
    "Malformed attempt ID was accepted"
  ensure (fileName noteA == repeated '1' 64 ++ ".claim")
    "Claim filename changed"
  ensure (← failed (claimAll root directId .batch hash [noteA, noteA]))
    "Duplicate batch selection reached private storage"
  ensure (← failed (claimAll root directId .direct hash []))
    "Empty direct selection reached private storage"
  ensure (← failed (claimAll root directId .direct "bad-hash" [noteA]))
    "Malformed operation hash reached private storage"

  let direct ← startClaimed root directId .direct hash [noteA]
  ensure (direct.nextSeq == 1 && direct.selected == [noteA])
    "Claimed direct attempt did not start"
  let loaded ← loadClaimed root directId .direct
  ensure (loaded.nextSeq == 1 && loaded.selected == [noteA])
    "Claimed direct attempt did not replay"
  ensure ((← readClaim root noteA) == sample)
    "Durable direct claim was not bound to the reviewed operation"
  ensure (← failed (startClaimed root secondId .direct hash [noteA]))
    "Another attempt claimed an already reserved note"
  ensure (← failed (startClaimed root directId .direct hash [noteA]))
    "Same-attempt restart silently reused an existing claim"
  let _ ← appendClaimed root directId .direct (.sign hash)
  let _ ← appendClaimed root directId .direct (.reserve noteA)
  let submitted ← armClaimedSubmission root directId .direct
  ensure (submitted.direct.sends == 1) "Claimed direct send was not armed once"
  ensure (← failed (armClaimedSubmission root directId .direct))
    "Claimed direct send was armed twice"
  let _ ← appendClaimed root directId .direct .unknown
  ensure (← failed (startClaimed root secondId .direct hash [noteA]))
    "Unknown outcome released a claimed note"

  let batch ← startClaimed root batchId .batch hash [noteB, noteC]
  ensure (batch.selected == [noteB, noteC]) "Batch selection was not recorded"
  ensure ((← readClaim root noteB).selected == [noteB, noteC] &&
      (← readClaim root noteC).selected == [noteB, noteC])
    "Batch claims did not bind the entire ordered selection"
  let _ ← appendClaimed root batchId .batch (.sign hash)
  let _ ← appendClaimed root batchId .batch (.reserve noteB)
  ensure (← failed (armClaimedSubmission root batchId .batch))
    "Partially reserved batch was exposed"
  let replayed ← loadClaimed root batchId .batch
  ensure (replayed.batch.reserved == [noteB])
    "Restart lost a partial batch reservation"
  let _ ← appendClaimed root batchId .batch (.reserve noteC)
  let armed ← armClaimedSubmission root batchId .batch
  ensure (armed.batch.sends == 1) "Fully claimed batch was not armed"

  let _ ← startClaimed root conflictId .direct hash [noteE]
  ensure (← failed (startClaimed root partialId .batch hash [noteD, noteE]))
    "Conflicting batch start was accepted"
  ensure ((← readClaim root noteD).attemptId == partialId)
    "Partial batch claim disappeared after a conflict"
  ensure (← failed (loadClaimed root partialId .batch))
    "An orphan claim was interpreted as a complete attempt"
  ensure (← failed (startClaimed root secondId .direct hash [noteD]))
    "Another attempt reused a partial batch claim"
  ensure (← failed (startClaimed root partialId .batch hash [noteD, noteE]))
    "Retry silently adopted a partial batch claim"

  let _ ← Tornado.Runtime.AttemptJournal.start
    (root ++ "/attempts") journalOnlyId .direct hash [noteF]
  ensure (← failed (loadClaimed root journalOnlyId .direct))
    "Journal without global note claim passed replay"
  ensure (← failed (appendClaimed root journalOnlyId .direct (.sign hash)))
    "Journal without global claim advanced"
  ensure (← failed (armClaimedSubmission root journalOnlyId .direct))
    "Journal without global claim was exposed"
  let otherClaim : Claim := ⟨secondId, .direct, hash, noteG, [noteG]⟩
  Tornado.Runtime.ProtectedIO.createPrivate
    (root ++ "/claims/" ++ fileName noteG) (encode otherClaim).toUTF8
  let _ ← Tornado.Runtime.AttemptJournal.start
    (root ++ "/attempts") secondId .direct hash [noteG]
  ensure ((← loadClaimed root secondId .direct).selected == [noteG])
    "Valid preexisting claim did not bind to its journal"

  Tornado.Runtime.ProtectedIO.createPrivate
    (root ++ "/claims/" ++ fileName noteH) "not-json".toUTF8
  ensure (← failed (readClaim root noteH))
    "Malformed claim file was accepted"
  ensure (← failed (startClaimed root mismatchId .direct hash [noteH]))
    "Malformed existing claim was overwritten"

  let wrongHash := "0x" ++ repeated 'b' 64
  let wrongClaim : Claim := ⟨mismatchId, .direct, wrongHash, noteI, [noteI]⟩
  Tornado.Runtime.ProtectedIO.createPrivate
    (root ++ "/claims/" ++ fileName noteI) (encode wrongClaim).toUTF8
  let _ ← Tornado.Runtime.AttemptJournal.start
    (root ++ "/attempts") mismatchId .direct hash [noteI]
  ensure (← failed (loadClaimed root mismatchId .direct))
    "Claim with a different reviewed operation hash passed replay"

  IO.println "Note claims: exclusive direct/batch reservations, replay, unknown, conflict and orphan checks passed"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [root] =>
        exercise root
        return (0 : UInt32)
    | ["claim-only", root, id, note] =>
        claimAll root id .direct ("0x" ++ repeated 'a' 64) [note]
        return (0 : UInt32)
    | ["read-claim", root, note] =>
        IO.println (← readClaim root note).attemptId
        return (0 : UInt32)
    | _ =>
        IO.eprintln "Expected a test root or claim-only/read-claim args"
        return (1 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)
