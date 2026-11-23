import Tornado.Runtime.AttemptJournal

open Tornado.Runtime.AttemptJournal

private def repeated (char : Char) (count : Nat) : String :=
  String.ofList (List.replicate count char)

private def ensure (condition : Bool) (description : String) : IO Unit :=
  unless condition do throw <| IO.userError description

private def failed (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

def main (args : List String) : IO Unit := do
  let base ← match args[0]? with
    | some path => pure path
    | none => throw <| IO.userError "Missing secure journal test directory"
  let hash := "0x" ++ repeated 'a' 64
  let receipt := "0x" ++ repeated 'b' 64
  let noteA := "0x" ++ repeated 'c' 64
  let noteB := "0x" ++ repeated 'd' 64
  let directId := repeated '1' 32
  let crashId := repeated '2' 32
  let batchId := repeated '3' 32
  let gapId := repeated '4' 32
  let malformedId := repeated '5' 32
  let strayId := repeated '6' 32

  let sample : Record := {
    attemptId := directId, kind := .direct, seq := 0,
    event := .prepare hash [noteA] }
  ensure ((decode (encode sample)).isOk) "Canonical record did not roundtrip"
  ensure (!(decode (encode sample ++ "\n")).isOk)
    "Noncanonical record was accepted"

  let initial ← start base directId .direct hash [noteA]
  ensure (initial.direct.phase == .approved && initial.nextSeq == 1)
    "Direct preparation was not durable"
  ensure (← failed (start base directId .direct hash [noteA]))
    "An attempt ID was overwritten"
  ensure (← failed (append base directId .direct .send))
    "Direct send without arming was accepted"
  let reloaded ← load base directId .direct
  ensure (reloaded.direct.phase == .approved && reloaded.nextSeq == 1)
    "Failed transition advanced direct state"
  let _ ← append base directId .direct (.sign hash)
  let reserved ← append base directId .direct (.reserve noteA)
  ensure (reserved.direct.phase == .reserved) "Direct reservation was not recorded"
  let submitted ← armSubmission base directId .direct
  ensure (submitted.direct.phase == .submitted && submitted.direct.sends == 1)
    "Exposure and send intents were not durably armed"
  let recovered ← load base directId .direct
  ensure (recovered.direct.phase == .submitted && recovered.direct.sends == 1 &&
      !Tornado.Policy.retryAllowed recovered.direct)
    "Restart lost the consumed send allowance"
  ensure (← failed (append base directId .direct .send))
    "Restart allowed a second direct send"
  ensure (← failed (append base directId .direct (.sign hash)))
    "Restart allowed replacement signing"
  let unknown ← append base directId .direct .unknown
  ensure (unknown.direct.phase == .unknown && !Tornado.Policy.retryAllowed unknown.direct)
    "Unknown direct outcome allowed retry"
  ensure (← failed (armSubmission base directId .direct))
    "Unknown direct attempt was rearmed"
  let confirmed ← append base directId .direct
    (.confirm hash receipt true true true [noteA])
  ensure (confirmed.direct.phase == .confirmed)
    "Exact direct confirmation was not recorded"

  let _ ← start base crashId .direct hash [noteA]
  let _ ← append base crashId .direct (.sign hash)
  let _ ← append base crashId .direct (.reserve noteA)
  let exposed ← append base crashId .direct .expose
  ensure (exposed.direct.phase == .exposed) "Exposure intent was not recorded"
  let crashed ← load base crashId .direct
  ensure (crashed.direct.phase == .exposed &&
      (← failed (append base crashId .direct .send)) &&
      (← failed (armSubmission base crashId .direct)))
    "Recovered exposure was allowed to send"
  let _ ← append base crashId .direct .unknown
  ensure (← failed (append base crashId .direct (.sign hash)))
    "Recovered unknown attempt was resigned"

  let _ ← start base batchId .batch hash [noteA, noteB]
  let _ ← append base batchId .batch (.sign hash)
  let partiallyReserved ← append base batchId .batch (.reserve noteA)
  ensure (partiallyReserved.batch.reserved == [noteA]) "Partial batch reservation was lost"
  let partialRestart ← load base batchId .batch
  ensure (partialRestart.batch.reserved == [noteA] &&
      (← failed (append base batchId .batch .expose)) &&
      (← failed (armSubmission base batchId .batch)))
    "Partial batch was exposed after restart"
  let _ ← append base batchId .batch (.reserve noteB)
  let batchSubmitted ← armSubmission base batchId .batch
  ensure (batchSubmitted.batch.phase == .submitted && batchSubmitted.batch.sends == 1)
    "Batch intents were not armed after all reservations"
  let _ ← append base batchId .batch .unknown
  ensure (← failed (append base batchId .batch (.reserve noteA)))
    "Unknown batch reserved a note again"
  let batchConfirmed ← append base batchId .batch
    (.confirm hash receipt true true true [noteB, noteA])
  ensure (batchConfirmed.batch.phase == .confirmed)
    "Exact batch confirmation was not recorded"

  let _ ← start base gapId .direct hash [noteA]
  let gap : Record := {
    attemptId := gapId, kind := .direct, seq := 2, event := .sign hash }
  Tornado.Runtime.ProtectedIO.createPrivate
    (base ++ "/" ++ fileName gapId 2) (encode gap).toUTF8
  ensure ((← failed (load base gapId .direct)) &&
      (← failed (append base gapId .direct (.sign hash))))
    "Sequence gap was treated as an absent tail"

  let _ ← start base malformedId .direct hash [noteA]
  Tornado.Runtime.ProtectedIO.createPrivate
    (base ++ "/" ++ fileName malformedId 1) "not-json".toUTF8
  ensure ((← failed (load base malformedId .direct)) &&
      (← failed (append base malformedId .direct (.sign hash))))
    "Malformed tail was ignored"

  let _ ← start base strayId .direct hash [noteA]
  Tornado.Runtime.ProtectedIO.createPrivate
    (base ++ "/" ++ strayId ++ ".bad.journal") "stray".toUTF8
  ensure (← failed (load base strayId .direct))
    "Unexpected attempt record name was ignored"

  IO.println "Attempt journal: durable replay, crash/retry, batch, gap and malformed-record checks passed"
