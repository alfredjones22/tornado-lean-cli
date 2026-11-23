import Tornado.Policy

open Tornado.Policy

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check : Except String Unit := do
  let approved ← stepAttempt {} (.approve "reviewed")
  let signed ← stepAttempt approved (.sign "reviewed")
  require ((stepAttempt signed .expose).isOk == false) "Unreserved attempt exposed"
  let reserved ← stepAttempt signed .reserve
  let exposed ← stepAttempt reserved .expose
  require (!retryAllowed exposed) "Exposed attempt allowed replacement"
  require ((stepAttempt exposed (.sign "replacement")).isOk == false)
    "Exposed attempt allowed a second signature"
  let evidence : ConfirmationEvidence := ⟨true, true, true⟩
  let relayed ← stepAttempt exposed (.confirm evidence)
  require (relayed.phase == .confirmed)
    "An operation relayed after exposure could not reconcile"
  let unknownAfterExposure ← stepAttempt exposed .markUnknown
  require (!retryAllowed unknownAfterExposure)
    "Unknown exposed attempt allowed retry"
  require ((stepAttempt unknownAfterExposure .send).isOk == false)
    "Unknown exposed attempt could send again"
  let confirmedUnknown ← stepAttempt unknownAfterExposure (.confirm evidence)
  require (confirmedUnknown.phase == .confirmed)
    "Unknown exposed attempt could not reconcile exact evidence"
  require ((stepAttempt exposed (.confirm { evidence with withdrawalEventMatches := false })).isOk == false)
    "Missing pool event confirmed"
  let submitted ← stepAttempt exposed .send
  require (submitted.sends == 1) "First send was not counted"
  require ((stepAttempt submitted .send).isOk == false) "Submitted attempt sent twice"
  let unknownAfterSend ← stepAttempt submitted .markUnknown
  require ((stepAttempt unknownAfterSend .send).isOk == false)
    "Unknown submitted attempt sent twice"

def main : IO UInt32 := do
  match check with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok _ =>
      IO.println "PASS: one-note reservation, exposure, unknown outcome, and exact confirmation gates"
      return 0
