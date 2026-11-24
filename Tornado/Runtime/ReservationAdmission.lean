import Lean

/-!
Initial per-note reservation admission is only an observation of opaque paths.
It is not an exclusive claim or a promise that a path stays absent. The later
protected O_EXCL creation remains authoritative if another process races.
-/

namespace Tornado.Runtime.ReservationAdmission

inductive Observation where
  | absent (path : String)
  | present (path : String)
  | queryFailed (path : String)
  deriving BEq, DecidableEq, Repr

def Observation.path : Observation → String
  | .absent path | .present path | .queryFailed path => path

inductive Outcome where
  | allAbsent | blocked
  deriving BEq, DecidableEq, Repr

/-- An absent reply issues the next query; any present or failed reply stops
the program immediately. There is no read-status, replace, release or send. -/
inductive Executes : List String → List Observation → Outcome → Prop where
  | done : Executes [] [] .allAbsent
  | absent (path : String) (tail : Executes paths trace outcome) :
      Executes (path :: paths) (.absent path :: trace) outcome
  | present (path : String) (paths : List String) :
      Executes (path :: paths) [.present path] .blocked
  | queryFailed (path : String) (paths : List String) :
      Executes (path :: paths) [.queryFailed path] .blocked

structure Report (paths : List String) where
  private mk ::
  trace : List Observation
  outcome : Outcome
  executed : Executes paths trace outcome

structure Effects where
  pathExists : String → IO Bool

/-- `pathExists` suppresses every metadata error. Use lstat-style metadata
instead: only ENOENT is absence, while symlinks count as occupied entries and
permission, I/O and other failures are propagated to the terminal query reply. -/
def entryExists (path : String) : IO Bool := do
  try
    let _ ← (System.FilePath.mk path).symlinkMetadata
    return true
  catch error =>
    match error with
    | .noFileOrDirectory .. => return false
    | _ => throw error

def nativeEffects : Effects := ⟨entryExists⟩

/-- The exact executable interpreter for the finite path program. Exceptions
around the query itself become terminal failed replies, never absence. -/
def runWith (effects : Effects) : (paths : List String) → IO (Report paths)
  | [] => pure ⟨[], .allAbsent, .done⟩
  | path :: paths => do
      let observation ← try
          let found ← effects.pathExists path
          pure (if found then Observation.present path else .absent path)
        catch _ => pure (.queryFailed path)
      match observation with
      | .present _ => return ⟨[.present path], .blocked, .present path paths⟩
      | .queryFailed _ => return ⟨[.queryFailed path], .blocked, .queryFailed path paths⟩
      | .absent _ =>
        let tail ← runWith effects paths
        return ⟨.absent path :: tail.trace, tail.outcome, .absent path tail.executed⟩

def ValidPaths (paths : Array String) : Prop :=
  0 < paths.size ∧ paths.size ≤ 12 ∧ paths.toList.eraseDups.length = paths.size ∧
    paths.all (fun path => path.startsWith "/" && path.length ≤ 4096) = true

instance (paths : Array String) : Decidable (ValidPaths paths) := by
  unfold ValidPaths
  infer_instance

/-- A successful observation certificate, indexed by the exact opaque paths.
This grants no persistence, release, replacement, or network capability. -/
structure CheckedAbsence (paths : Array String) where
  private mk ::
  valid : ValidPaths paths
  report : Report paths.toList
  observed : report.outcome = .allAbsent

private def invalidScope : String := "Invalid withdrawal reservation path selection."
private def blocked : String :=
  "A selected note already has a reservation, or its status path could not be checked. Reconcile existing status files before preparing another withdrawal."

def requireUnclaimedWith (effects : Effects) (paths : Array String) : IO (CheckedAbsence paths) := do
  if valid : ValidPaths paths then
    let report ← runWith effects paths.toList
    if observed : report.outcome = .allAbsent then
      return ⟨valid, report, observed⟩
    else throw <| IO.userError blocked
  else throw <| IO.userError invalidScope

def requireUnclaimed (paths : Array String) : IO (CheckedAbsence paths) :=
  requireUnclaimedWith nativeEffects paths

theorem executed_all_absent (paths : List String) (trace : List Observation)
    (execution : Executes paths trace .allAbsent) : trace = paths.map Observation.absent := by
  induction paths generalizing trace with
  | nil => cases execution; rfl
  | cons path paths ih =>
    cases execution with
    | absent _ tail => simpa using congrArg (Observation.absent path :: ·) (ih _ tail)

theorem executed_query_prefix (paths : List String) (trace : List Observation) (outcome : Outcome)
    (execution : Executes paths trace outcome) :
    (trace.map Observation.path).IsPrefix paths := by
  induction execution with
  | done => exact ⟨[], rfl⟩
  | absent path tail ih =>
      obtain ⟨rest, equal⟩ := ih
      exact ⟨rest, by simpa [Observation.path] using congrArg (path :: ·) equal⟩
  | present path paths => exact ⟨paths, rfl⟩
  | queryFailed path paths => exact ⟨paths, rfl⟩

theorem executed_query_count (paths : List String) (trace : List Observation) (outcome : Outcome)
    (execution : Executes paths trace outcome) : trace.length ≤ paths.length := by
  obtain ⟨rest, equal⟩ := executed_query_prefix paths trace outcome execution
  have sizes := congrArg List.length equal
  simp only [List.length_append, List.length_map] at sizes
  omega

theorem executed_blocked_terminal (paths : List String) (trace : List Observation) (outcome : Outcome)
    (execution : Executes paths trace outcome) (blocked : outcome = .blocked) :
    ∃ (priorPaths : List String) (last : String), trace = priorPaths.map Observation.absent ++ [.present last] ∨
      trace = priorPaths.map Observation.absent ++ [.queryFailed last] := by
  induction execution with
  | done => contradiction
  | absent path tail ih =>
    obtain ⟨priorPaths, last, terminal⟩ := ih blocked
    refine ⟨path :: priorPaths, last, ?_⟩
    rcases terminal with terminal | terminal
    · exact Or.inl (by simpa using congrArg (Observation.absent path :: ·) terminal)
    · exact Or.inr (by simpa using congrArg (Observation.absent path :: ·) terminal)
  | present path paths => exact ⟨[], path, Or.inl rfl⟩
  | queryFailed path paths => exact ⟨[], path, Or.inr rfl⟩

theorem checked_exact_absence (paths : Array String) (checked : CheckedAbsence paths) :
    checked.report.trace = paths.toList.map Observation.absent := by
  apply executed_all_absent paths.toList checked.report.trace
  simpa [checked.observed] using checked.report.executed

theorem checked_bounded_queries (paths : Array String) (checked : CheckedAbsence paths) :
    checked.report.trace.length = paths.size ∧ 0 < paths.size ∧ paths.size ≤ 12 := by
  rw [checked_exact_absence paths checked]
  exact ⟨by simp, checked.valid.1, checked.valid.2.1⟩

theorem present_not_all_absent (path : String) (paths : List String) :
    ¬ Executes (path :: paths) [.present path] .allAbsent := by
  intro execution
  have exact := executed_all_absent _ _ execution
  simp at exact

theorem failed_not_all_absent (path : String) (paths : List String) :
    ¬ Executes (path :: paths) [.queryFailed path] .allAbsent := by
  intro execution
  have exact := executed_all_absent _ _ execution
  simp at exact

end Tornado.Runtime.ReservationAdmission

#print axioms Tornado.Runtime.ReservationAdmission.executed_all_absent
#print axioms Tornado.Runtime.ReservationAdmission.executed_query_prefix
#print axioms Tornado.Runtime.ReservationAdmission.executed_query_count
#print axioms Tornado.Runtime.ReservationAdmission.executed_blocked_terminal
#print axioms Tornado.Runtime.ReservationAdmission.checked_exact_absence
#print axioms Tornado.Runtime.ReservationAdmission.checked_bounded_queries
#print axioms Tornado.Runtime.ReservationAdmission.present_not_all_absent
#print axioms Tornado.Runtime.ReservationAdmission.failed_not_all_absent
