import Lean
import Tornado.Domain.Status

open Lean Tornado.Domain

private def repeated (char : Char) (count : Nat) : String :=
  "0x" ++ String.ofList (List.replicate count char)

private def fields : List (String × Json) := [
  ("version", toJson (1 : Nat)),
  ("kind", toJson "one-note-4337"),
  ("chainId", toJson (1 : Nat)),
  ("userOpHash", toJson (repeated 'a' 64)),
  ("entryPointAddress", toJson (repeated '1' 40)),
  ("sender", toJson (repeated '2' 40)),
  ("paymaster", toJson (repeated '3' 40)),
  ("nonce", toJson "0x0"),
  ("poolAddress", toJson (repeated '4' 40)),
  ("recipient", toJson (repeated '5' 40)),
  ("fee", toJson "0x100"),
  ("nullifierHash", toJson (repeated 'b' 64)),
  ("fromBlock", toJson "0x10"),
  ("status", toJson "unknown")
]

private def replace (rows : List (String × Json)) (key : String) (value : Json) : List (String × Json) :=
  rows.map (fun (name, previous) => if name == key then (name, value) else (name, previous))

private def decoded (rows : List (String × Json)) : Except String WithdrawalStatusRecord :=
  decodeWithdrawalStatus (Json.mkObj rows).compress

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check : Except String Unit := do
  let legacy ← decoded fields
  require (!canPrepareNewAttempt (some legacy) false) "Unknown legacy attempt can retry"
  require (!canPrepareNewAttempt (some legacy) true) "Unknown legacy attempt can retry with flag"
  let rejected ← decoded (replace fields "status" (toJson "rejected"))
  require (canPrepareNewAttempt (some rejected) true) "Legacy rejected retry blocked"
  require (!canPrepareNewAttempt (some rejected) false) "Legacy rejected retry needs no flag"

  let signedRows := fields ++ [("candidates", toJson #[Json.mkObj fields])]
  let signed ← decoded signedRows
  require (!canPrepareNewAttempt (some signed) false) "Signed candidate can retry"
  require (!canPrepareNewAttempt (some signed) true) "Signed candidate can retry with flag"
  let signedRejected ← decoded ((replace fields "status" (toJson "rejected")) ++
    [("candidates", toJson #[Json.mkObj fields])])
  require (!canPrepareNewAttempt (some signedRejected) true) "Rejected signed candidate can retry"

  require ((decoded (replace fields "version" (toJson (2 : Nat)))).isOk == false) "Wrong version accepted"
  require ((decoded (replace fields "kind" (toJson "batch-4337"))).isOk == false) "Wrong kind accepted"
  require ((decoded (replace fields "userOpHash" (toJson "0xabc"))).isOk == false) "Short hash accepted"
  require ((decoded (fields ++ [("candidates", toJson #[Json.mkObj fields, Json.mkObj fields])])).isOk == false)
    "Duplicate candidate hash accepted"
  let differentSender := Json.mkObj (replace fields "sender" (toJson (repeated '8' 40)))
  require ((decoded (fields ++ [("candidates", toJson #[differentSender])])).isOk == false)
    "Candidate with different sender accepted"
  require ((decodeWithdrawalStatus "not JSON").isOk == false) "Malformed JSON accepted"

  let unknown := legacy.current
  let confirmed := { unknown with status := .confirmed }
  let pending := { unknown with status := .pending }
  let failed := { unknown with status := .failed }
  let some aggregate := aggregateCandidate [unknown, pending, confirmed, failed]
    | throw "No candidate aggregate"
  require (aggregate.status == .confirmed) "Confirmed candidate lost priority"
  let some aggregate := aggregateCandidate [failed, pending, unknown]
    | throw "No candidate aggregate"
  require (aggregate.status == .unknown) "Unknown candidate lost priority"

def main : IO UInt32 := do
  match check with
  | .ok _ =>
      IO.println "PASS: decoded status records, rejected malformed candidates, and blocked signed replacement"
      return 0
  | .error error =>
      IO.eprintln error
      return 1
