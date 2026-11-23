import Tornado.Policy.Batch

open Tornado.Policy.Batch

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check : Except String Unit := do
  let fresh : Attempt := {}
  require (!validSelection []) "Empty batch selected"
  require (!validSelection ["a", "a"]) "Duplicate note selected"
  require (!validSelection (List.replicate 13 "a")) "Oversized batch selected"
  let reviewed ← step fresh (.prepare ["a", "b"] "reviewed")
  let signed ← step reviewed (.sign "reviewed")
  require ((step reviewed (.sign "altered")).isOk == false) "Changed payload signed"
  require ((step signed .expose).isOk == false) "Unreserved batch exposed"
  let one ← step signed (.reserveNote "a")
  require ((step one .expose).isOk == false) "Partly reserved batch exposed"
  require ((step one (.reserveNote "a")).isOk == false) "Duplicate reservation accepted"
  require ((step one (.reserveNote "c")).isOk == false) "Foreign note reserved"
  let all ← step one (.reserveNote "b")
  let exposed ← step all .expose
  require ((step exposed (.sign "reviewed")).isOk == false) "Exposed batch re-signed"
  let simulatedUnknown ← step exposed .markUnknown
  require (!retryAllowed simulatedUnknown) "Simulation-exposed attempt allowed retry"
  let relayEvidence : Evidence := { receiptSuccess := true, entryPointEventMatches := true, userOpHash := "reviewed", matchedNullifiers := ["a", "b"] }
  let relayed ← step exposed (.confirm relayEvidence)
  require (relayed.phase == .confirmed) "Simulation RPC relay could not reconcile"
  let submitted ← step exposed .send
  require (submitted.sends == 1) "Send count changed"
  require ((step submitted .send).isOk == false) "Second send accepted"
  let unknown ← step submitted .markUnknown
  require (!retryAllowed unknown) "Unknown attempt allowed retry"
  let incomplete : Evidence := { receiptSuccess := true, entryPointEventMatches := true, userOpHash := "reviewed", matchedNullifiers := ["a"] }
  require ((step unknown (.confirm incomplete)).isOk == false) "Missing withdrawal event confirmed"
  require (!exactEvents ["a", "b"] ["a", "a"]) "Duplicate event accepted"
  let correct := { incomplete with matchedNullifiers := ["b", "a"] }
  let confirmed ← step unknown (.confirm correct)
  require (confirmed.phase == .confirmed) "Exact batch confirmation rejected"
  require ((step unknown (.confirm { correct with receiptSuccess := false })).isOk == false)
    "Failed receipt confirmed"
  require ((step unknown (.confirm { correct with entryPointEventMatches := false })).isOk == false)
    "Missing EntryPoint event confirmed"
  require ((step unknown (.confirm { correct with userOpHash := "other" })).isOk == false)
    "Different UserOperation hash confirmed"

def main : IO UInt32 := do
  match check with
  | .ok _ =>
      IO.println "PASS: batch reservation, exposure, single send, and exact confirmation gates"
      return 0
  | .error message =>
      IO.eprintln message
      return 1
