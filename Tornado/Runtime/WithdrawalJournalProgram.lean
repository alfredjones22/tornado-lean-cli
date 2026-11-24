import Tornado.Runtime.ProtectedIO

/-! Finite protected-file programs used by production journal adapters. A
callback acknowledgement is an observation, never a proof of physical fsync.
The separate physical model admits a completed write whose reply was lost. -/

namespace Tornado.Runtime.WithdrawalJournalProgram

inductive Command where
  | create (path : String) (contents : ByteArray)
  | replace (path : String) (expected contents : ByteArray)
  deriving Inhabited, BEq

abbrev Program := List Command

inductive Reply where
  | acknowledged | failed
  deriving Inhabited, BEq, DecidableEq

structure Observation where
  command : Command
  reply : Reply
  deriving BEq

/-- The attempted commands are an ordered prefix; failure is terminal. -/
inductive Executes : Program → List Observation → Bool → Prop where
  | done : Executes [] [] false
  | acknowledged (command : Command) {rest : Program} {trace : List Observation}
      {stopped : Bool} (tail : Executes rest trace stopped) :
      Executes (command :: rest) (⟨command, .acknowledged⟩ :: trace) stopped
  | failed (command : Command) (rest : Program) :
      Executes (command :: rest) [⟨command, .failed⟩] true

structure Effects where
  createPrivate : String → ByteArray → IO Unit
  replacePrivate : String → ByteArray → ByteArray → IO Unit

def protectedEffects : Effects :=
  ⟨ProtectedIO.createPrivate, ProtectedIO.replacePrivate⟩

private def dispatch (effects : Effects) : Command → IO Unit
  | .create path bytes => effects.createPrivate path bytes
  | .replace path expected bytes => effects.replacePrivate path expected bytes

structure Report (program : Program) where
  private mk ::
  trace : List Observation
  stopped : Bool
  executed : Executes program trace stopped
  failure : Option IO.Error

def acknowledgedCommands : List Observation → Program
  | [] => []
  | observation :: rest => match observation.reply with
    | .acknowledged => observation.command :: acknowledgedCommands rest
    | .failed => acknowledgedCommands rest

def Report.completedCommands {program : Program} (report : Report program) : Program :=
  acknowledgedCommands report.trace

def Report.allSucceeded {program : Program} (report : Report program) : Bool :=
  !report.stopped

/-- The only production dispatcher for these finite file commands. Exceptions
are observed conservatively: they may occur before or after a physical write.
No command after a failed reply is dispatched. -/
def runIO (effects : Effects) : (program : Program) → IO (Report program)
  | [] => pure ⟨[], false, .done, none⟩
  | command :: rest => do
    let result : Except IO.Error Unit ← try
      dispatch effects command
      pure (Except.ok () : Except IO.Error Unit)
    catch error => pure (Except.error error : Except IO.Error Unit)
    match result with
    | .ok () =>
      let tail ← runIO effects rest
      pure ⟨⟨command, .acknowledged⟩ :: tail.trace, tail.stopped,
        .acknowledged command tail.executed, tail.failure⟩
    | .error error => pure ⟨[⟨command, .failed⟩], true, .failed command rest, some error⟩

/-- A returned acknowledgement carries the complete actual dispatch trace.
The physical interpretation still requires the Effects callback contract. -/
structure Acknowledged (program : Program) where
  private mk ::
  trace : List Observation
  executed : Executes program trace false

private def acknowledge {program : Program} (report : Report program) :
    Except String (Acknowledged program) :=
  if complete : report.stopped = false then
    .ok ⟨report.trace, complete ▸ report.executed⟩
  else .error "Protected journal program stopped before complete acknowledgement."

def requireSuccess {program : Program} (report : Report program) : IO (Acknowledged program) :=
  match acknowledge report with
  | .ok receipt => pure receipt
  | .error message => throw <| report.failure.getD (IO.userError message)

def runCreate (effects : Effects) (path : String) (contents : ByteArray) :
    IO (Acknowledged [.create path contents]) := do
  let report ← runIO effects [.create path contents]
  requireSuccess report

def runReplace (effects : Effects) (path : String) (expected contents : ByteArray) :
    IO (Acknowledged [.replace path expected contents]) := do
  let report ← runIO effects [.replace path expected contents]
  requireSuccess report

/-- Production single-file adapters share the same dispatch and conservative
failure semantics as the mirrored withdrawal journal. Lock removal remains a
separate, explicitly reviewed operation. -/
def createProtected (path : String) (contents : ByteArray) : IO Unit := do
  let _ ← runCreate protectedEffects path contents
  pure ()

def replaceProtected (path : String) (expected contents : ByteArray) : IO Unit := do
  let _ ← runReplace protectedEffects path expected contents
  pure ()

/-- The exact command and byte sequence is retained, rather than only hashes
or a caller-supplied `durable` flag. -/
theorem successful_trace (program : Program) (trace : List Observation)
    (executed : Executes program trace false) :
    trace = program.map (fun command => ⟨command, .acknowledged⟩) := by
  induction program generalizing trace with
  | nil => cases executed; rfl
  | cons command rest ih =>
    cases executed with
    | acknowledged _ tail => simp only [List.map_cons]; rw [ih _ tail]

theorem acknowledged_exact_commands (program : Program) (receipt : Acknowledged program) :
    acknowledgedCommands receipt.trace = program := by
  rw [successful_trace program receipt.trace receipt.executed]
  clear receipt
  induction program with
  | nil => rfl
  | cons command rest ih => simp [acknowledgedCommands, ih]

theorem attempted_prefix (program : Program) (trace : List Observation) (stopped : Bool)
    (executed : Executes program trace stopped) :
    ∃ rest, program = trace.map (·.command) ++ rest := by
  induction executed with
  | done => exact ⟨[], rfl⟩
  | acknowledged command tail ih =>
    obtain ⟨rest, equal⟩ := ih
    exact ⟨rest, by simp [equal]⟩
  | failed command rest => exact ⟨rest, rfl⟩

theorem failed_trace (program : Program) (trace : List Observation) (stopped : Bool)
    (executed : Executes program trace stopped) (failure : stopped = true) :
    ∃ before command after,
      program = before ++ command :: after ∧
      trace = before.map (fun cmd => ⟨cmd, .acknowledged⟩) ++ [⟨command, .failed⟩] := by
  induction executed with
  | done => contradiction
  | acknowledged command tail ih =>
    obtain ⟨before, failed, after, original, observed⟩ := ih failure
    exact ⟨command :: before, failed, after, by simp [original], by simp [observed]⟩
  | failed command rest => exact ⟨[], command, rest, rfl, rfl⟩

end Tornado.Runtime.WithdrawalJournalProgram

#print axioms Tornado.Runtime.WithdrawalJournalProgram.successful_trace
#print axioms Tornado.Runtime.WithdrawalJournalProgram.acknowledged_exact_commands
#print axioms Tornado.Runtime.WithdrawalJournalProgram.attempted_prefix
#print axioms Tornado.Runtime.WithdrawalJournalProgram.failed_trace

namespace Tornado.Runtime.WithdrawalJournalProgram.Physical

/-- This is an explicit abstract file-content contract, not an OS model. Safe
paths, exclusive creation, protected permissions, fsync and CAS implementation
must be supplied by the ProtectedIO boundary. -/
abbrev Store := String → Option (Array UInt8)

private def put (before : Store) (path : String) (bytes : ByteArray) : Store :=
  fun query => if query = path then some bytes.data else before query

def apply (command : Command) (before : Store) : Except String Store :=
  match command with
  | .create path bytes =>
    if before path = none then .ok (put before path bytes)
    else .error "Exclusive journal path is occupied."
  | .replace path expected bytes =>
    if before path = some expected.data then .ok (put before path bytes)
    else .error "Journal compare-and-replace differs from expected bytes."

inductive Outcome where
  | acknowledged | failedBeforeWrite | completedLostReply
  deriving BEq, DecidableEq

structure Observation where
  command : Command
  outcome : Outcome

def Observation.visible (event : Observation) : WithdrawalJournalProgram.Observation :=
  ⟨event.command, if event.outcome == .acknowledged then .acknowledged else .failed⟩

/-- A failed callback admits either no completed write, or one completed
write with no acknowledgement. Both branches stop the production program. -/
inductive Executes : Program → List Observation → Store → Store → Bool → Prop where
  | done (store : Store) : Executes [] [] store store false
  | acknowledged (command : Command) {rest : Program} {trace : List Observation}
      {before middle after : Store} {stopped : Bool}
      (write : apply command before = .ok middle)
      (tail : Executes rest trace middle after stopped) :
      Executes (command :: rest) (⟨command, .acknowledged⟩ :: trace) before after stopped
  | failedBeforeWrite (command : Command) (rest : Program) (before : Store) :
      Executes (command :: rest) [⟨command, .failedBeforeWrite⟩] before before true
  | completedLostReply (command : Command) (rest : Program) {before after : Store}
      (write : apply command before = .ok after) :
      Executes (command :: rest) [⟨command, .completedLostReply⟩] before after true

def appliedCommands : List Observation → Program
  | [] => []
  | event :: rest => match event.outcome with
    | .failedBeforeWrite => appliedCommands rest
    | _ => event.command :: appliedCommands rest

def applyAll : Program → Store → Except String Store
  | [], before => .ok before
  | command :: rest, before => do applyAll rest (← apply command before)

theorem visible_trace (program : Program) (trace : List Observation)
    (before after : Store) (stopped : Bool)
    (physical : Executes program trace before after stopped) :
    WithdrawalJournalProgram.Executes program (trace.map Observation.visible) stopped := by
  induction physical with
  | done => exact .done
  | acknowledged command write tail ih => exact .acknowledged command ih
  | failedBeforeWrite command rest store => exact .failed command rest
  | completedLostReply command rest write => exact .failed command rest

/-- A crash/lost reply can leave exactly a completed original prefix. No
later command, reordered command, substituted path or substituted bytes enters
this explicit physical contract. -/
theorem applied_prefix (program : Program) (trace : List Observation)
    (before after : Store) (stopped : Bool)
    (physical : Executes program trace before after stopped) :
    ∃ rest, program = appliedCommands trace ++ rest := by
  induction physical with
  | done => exact ⟨[], rfl⟩
  | acknowledged command write tail ih =>
    obtain ⟨rest, equal⟩ := ih
    exact ⟨rest, by simp [appliedCommands, equal]⟩
  | failedBeforeWrite command rest store => exact ⟨command :: rest, rfl⟩
  | completedLostReply command rest write => exact ⟨rest, rfl⟩

theorem crash_state_exact_prefix (program : Program) (trace : List Observation)
    (before after : Store) (stopped : Bool)
    (physical : Executes program trace before after stopped) :
    applyAll (appliedCommands trace) before = .ok after := by
  induction physical with
  | done => rfl
  | acknowledged command write tail ih =>
    simpa [appliedCommands, applyAll, write, bind, Except.bind, pure, Except.pure] using ih
  | failedBeforeWrite command rest store => rfl
  | completedLostReply command rest write => simp [appliedCommands, applyAll, write, bind, Except.bind]

theorem create_exact_bytes (path : String) (bytes : ByteArray) (before after : Store)
    (write : apply (.create path bytes) before = .ok after) :
    before path = none ∧ after path = some bytes.data ∧
      ∀ query, query ≠ path → after query = before query := by
  simp only [apply] at write
  split at write
  · rename_i vacant
    cases write
    exact ⟨vacant, by simp [put], fun query different => by simp [put, different]⟩
  · contradiction

theorem replace_exact_bytes (path : String) (expected bytes : ByteArray) (before after : Store)
    (write : apply (.replace path expected bytes) before = .ok after) :
    before path = some expected.data ∧ after path = some bytes.data ∧
      ∀ query, query ≠ path → after query = before query := by
  simp only [apply] at write
  split at write
  · rename_i previous
    cases write
    exact ⟨previous, by simp [put], fun query different => by simp [put, different]⟩
  · contradiction

theorem write_never_deletes (command : Command) (before after : Store) (path : String)
    (write : apply command before = .ok after) (occupied : (before path).isSome = true) :
    (after path).isSome = true := by
  cases command with
  | create target bytes =>
    have exact := create_exact_bytes target bytes before after write
    by_cases same : path = target
    · subst path; simp [exact.2.1]
    · simpa [exact.2.2 path same] using occupied
  | replace target expected bytes =>
    have exact := replace_exact_bytes target expected bytes before after write
    by_cases same : path = target
    · subst path; simp [exact.2.1]
    · simpa [exact.2.2 path same] using occupied

theorem crash_never_deletes (program : Program) (trace : List Observation)
    (before after : Store) (stopped : Bool) (path : String)
    (physical : Executes program trace before after stopped)
    (occupied : (before path).isSome = true) : (after path).isSome = true := by
  induction physical with
  | done => exact occupied
  | acknowledged command write tail ih => exact ih (write_never_deletes command _ _ path write occupied)
  | failedBeforeWrite command rest store => exact occupied
  | completedLostReply command rest write => exact write_never_deletes command _ _ path write occupied

/-- Even an unacknowledged completed create leaves its claim occupied. An
absence observation before another process's create never authorizes reuse. -/
theorem occupied_blocks_readmission (path : String) (bytes : ByteArray) (store : Store)
    (occupied : (store path).isSome = true) :
    apply (.create path bytes) store = .error "Exclusive journal path is occupied." := by
  cases observed : store path with
  | none => simp [observed] at occupied
  | some existing => simp [apply, observed]

end Tornado.Runtime.WithdrawalJournalProgram.Physical

#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.visible_trace
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.applied_prefix
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.crash_state_exact_prefix
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.create_exact_bytes
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.replace_exact_bytes
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.write_never_deletes
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.crash_never_deletes
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.occupied_blocks_readmission

namespace Tornado.Runtime.WithdrawalJournalProgram.Physical

inductive UnavailableReason where
  | protectedPath | unreadableClaim | unavailableDirectory | staleReplaceLock
  deriving BEq, DecidableEq

/-- An in-flight create is allowed to leave incomplete or unreadable bytes.
The contents are intentionally unconstrained. A blocked syscall, including a
stale CAS lock, can leave the prior file map unchanged. This relation does not
model corruption/deletion of previously completed protected files. -/
inductive InFlightCrash : Command → Store → Store → Prop where
  | createInterrupted (path : String) (intended fragment : ByteArray) (before : Store)
      (vacant : before path = none) :
      InFlightCrash (.create path intended) before (put before path fragment)
  | replaceRenamed (path : String) (expected contents : ByteArray) (before after : Store)
      (renamed : apply (.replace path expected contents) before = .ok after) :
      InFlightCrash (.replace path expected contents) before after
  | blocked (command : Command) (before : Store) (reason : UnavailableReason) :
      InFlightCrash command before before

/-- The process may stop after complete writes and during its next syscall.
There is no callback success for the in-flight command. The physical prefix
can be followed by an occupied incomplete create, rather than complete bytes. -/
structure CrashPrefix (program : Program) (before after : Store) where
  completed : Program
  command : Command
  remaining : Program
  settled : Store
  completedTrace : List Observation
  original : program = completed ++ command :: remaining
  writes : Executes completed completedTrace before settled false
  interrupted : InFlightCrash command settled after

/-- All completed commands precede the unique interrupted command. A process
crash has no whole-program acknowledgement, even when the final file happens
to contain all intended bytes. -/
theorem interrupted_has_no_complete_ack (program : Program) (before after : Store)
    (crash : CrashPrefix program before after) :
    ¬ WithdrawalJournalProgram.Executes program
      (crash.completed.map (fun cmd => ⟨cmd, .acknowledged⟩)) false := by
  intro complete
  have same := successful_trace program _ complete
  have lengths := congrArg List.length same
  simp only [List.length_map] at lengths
  have originalLength := congrArg List.length crash.original
  simp only [List.length_append, List.length_cons] at originalLength
  omega

/-- The interrupted syscall cannot erase any previously occupied path. Its
new incomplete claim can still make subsequent exclusive creation fail. -/
theorem inflight_never_deletes (command : Command) (before after : Store) (path : String)
    (interrupted : InFlightCrash command before after)
    (occupied : (before path).isSome = true) : (after path).isSome = true := by
  cases interrupted with
  | createInterrupted target intended fragment store vacant =>
    by_cases same : path = target
    · simp [put, same]
    · simpa [put, same] using occupied
  | replaceRenamed target expected contents before after renamed =>
    exact write_never_deletes (.replace target expected contents) before after path renamed occupied
  | blocked command store reason => exact occupied

theorem crash_prefix_never_deletes (program : Program) (before after : Store)
    (crash : CrashPrefix program before after) (path : String)
    (occupied : (before path).isSome = true) : (after path).isSome = true :=
  inflight_never_deletes crash.command crash.settled after path crash.interrupted
    (crash_never_deletes crash.completed crash.completedTrace before crash.settled false path
      crash.writes occupied)

/-- The kernel-visible completed prefix has exactly its original commands;
the additional interrupted slot is deliberately excluded from this theorem. -/
theorem crash_completed_prefix_exact (program : Program) (before after : Store)
    (crash : CrashPrefix program before after) :
    applyAll (appliedCommands crash.completedTrace) before = .ok crash.settled ∧
    ∃ rest, program = appliedCommands crash.completedTrace ++ rest := by
  constructor
  · exact crash_state_exact_prefix crash.completed crash.completedTrace before crash.settled false crash.writes
  · obtain ⟨rest, completePrefix⟩ :=
      applied_prefix crash.completed crash.completedTrace before crash.settled false crash.writes
    exact ⟨rest ++ crash.command :: crash.remaining, crash.original.trans (by
      simpa only [List.append_assoc] using
        congrArg (fun completedPart => completedPart ++ crash.command :: crash.remaining) completePrefix)⟩

theorem interrupted_create_blocks_readmission (path : String) (fragment retry : ByteArray)
    (store : Store) :
    apply (.create path retry) (put store path fragment) =
      .error "Exclusive journal path is occupied." := by
  apply occupied_blocks_readmission
  simp [put]

end Tornado.Runtime.WithdrawalJournalProgram.Physical

#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.interrupted_has_no_complete_ack
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.inflight_never_deletes
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.crash_prefix_never_deletes
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.crash_completed_prefix_exact
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.interrupted_create_blocks_readmission

namespace Tornado.Runtime.WithdrawalJournalProgram.Physical

theorem create_preserves_occupied (target : String) (bytes : ByteArray) (before after : Store)
    (write : apply (.create target bytes) before = .ok after) (path : String)
    (previous : Array UInt8) (occupied : before path = some previous) :
    after path = some previous := by
  have exact := create_exact_bytes target bytes before after write
  by_cases same : path = target
  · subst path
    rw [exact.1] at occupied
    contradiction
  · rw [exact.2.2 path same]
    exact occupied

/-- A complete exclusive-create mirror program writes the exact complete
bytes to every selected path. Any previously occupied path keeps its exact
content; in particular, a selected occupied path makes completion impossible. -/
theorem complete_create_program (paths : List String) (bytes : ByteArray)
    (trace : List Observation) (before after : Store)
    (physical : Executes (paths.map (fun path => .create path bytes)) trace before after false) :
    (∀ path, path ∈ paths → after path = some bytes.data) ∧
    (∀ path previous, before path = some previous → after path = some previous) := by
  induction paths generalizing trace before after with
  | nil =>
    cases physical
    exact ⟨fun _ member => by contradiction, fun _ _ occupied => occupied⟩
  | cons path rest ih =>
    cases physical with
    | acknowledged command write tail =>
      obtain ⟨remaining, preserved⟩ := ih _ _ _ tail
      have created := create_exact_bytes path bytes _ _ write
      constructor
      · intro query member
        cases member with
        | head => exact preserved path bytes.data created.2.1
        | tail _ selected => exact remaining query selected
      · intro query previous occupied
        exact preserved query previous
          (create_preserves_occupied path bytes _ _ write query previous occupied)

end Tornado.Runtime.WithdrawalJournalProgram.Physical

#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.create_preserves_occupied
#print axioms Tornado.Runtime.WithdrawalJournalProgram.Physical.complete_create_program
