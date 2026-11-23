import Tornado.Spec.Refinement

open Tornado.Spec

private def directReviewed : Tornado.Policy.Attempt :=
  { phase := .approved, reviewedHash := some "h" }

private def directSigned : Tornado.Policy.Attempt :=
  { phase := .signed, reviewedHash := some "h", signedHash := some "h" }

private def directReserved : Tornado.Policy.Attempt :=
  { phase := .reserved, reviewedHash := some "h", signedHash := some "h",
    reservedHash := some "h" }

/-- A concrete run reaches the premise of `direct_exposure_refines_spec`.
    This guards against a vacuous theorem about an unreachable phase. -/
example : DirectRun [.approve "h", .sign "h", .reserve] directReserved := by
  exact DirectRun.append
    (DirectRun.append
      (DirectRun.append DirectRun.initial (.approve "h") (by rfl))
      (.sign "h") (by rfl))
    .reserve (by rfl)

private def batchReviewed : Tornado.Policy.Batch.Attempt :=
  { phase := .reviewed, selected := ["n1", "n2"], reviewedHash := some "h" }

private def batchSigned : Tornado.Policy.Batch.Attempt :=
  { phase := .signed, selected := ["n1", "n2"],
    reviewedHash := some "h", signedHash := some "h" }

private def batchFirstReserved : Tornado.Policy.Batch.Attempt :=
  { phase := .reserving, selected := ["n1", "n2"],
    reviewedHash := some "h", signedHash := some "h", reserved := ["n1"] }

private def batchAllReserved : Tornado.Policy.Batch.Attempt :=
  { phase := .reserving, selected := ["n1", "n2"],
    reviewedHash := some "h", signedHash := some "h", reserved := ["n1", "n2"] }

/-- Both reservations are reached through the native batch gate. -/
example : BatchRun [.prepare ["n1", "n2"] "h", .sign "h",
    .reserveNote "n1", .reserveNote "n2"] batchAllReserved := by
  exact BatchRun.append
    (BatchRun.append
      (BatchRun.append
        (BatchRun.append BatchRun.initial (.prepare ["n1", "n2"] "h") (by rfl))
        (.sign "h") (by rfl))
      (.reserveNote "n1") (by rfl))
    (.reserveNote "n2") (by rfl)

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check : Except String Unit := do
  let dExposed ← Tornado.Policy.stepAttempt directReserved .expose
  let dSubmitted ← Tornado.Policy.stepAttempt dExposed .send
  require (dSubmitted.sends == 1) "Direct first send was not recorded"
  require (!(Tornado.Policy.stepAttempt dSubmitted .send).isOk)
    "Direct second send was accepted"
  let dUnknown ← Tornado.Policy.stepAttempt dSubmitted .markUnknown
  require (!Tornado.Policy.retryAllowed dUnknown) "Direct unknown retry was accepted"
  let bExposed ← Tornado.Policy.Batch.step batchAllReserved .expose
  let bSubmitted ← Tornado.Policy.Batch.step bExposed .send
  require (bSubmitted.sends == 1) "Batch first send was not recorded"
  require (!(Tornado.Policy.Batch.step bSubmitted .send).isOk)
    "Batch second send was accepted"
  let bUnknown ← Tornado.Policy.Batch.step bSubmitted .markUnknown
  require (!Tornado.Policy.Batch.retryAllowed bUnknown) "Batch unknown retry was accepted"

def main : IO UInt32 := do
  match check with
  | .ok _ =>
    IO.println "PASS: concrete one-note and batch traces reach reservations and reject second sends"
    return 0
  | .error error =>
    IO.eprintln error
    return 1
