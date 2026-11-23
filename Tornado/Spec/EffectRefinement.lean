import Tornado.Spec.Effects
import Tornado.Spec.Refinement

namespace Tornado.Spec.Effects

/-- Every acknowledged reservation in a driver state must have a corresponding
    durable-reservation event in that state's earlier effect log. This becomes
    a useful trace invariant only for states reached from the empty driver. -/
def ReservationRecorded (state : State) : Prop :=
  ∀ hash, state.acknowledged = some hash →
    Effect.durableReservation hash ∈ state.effects

inductive Run (config : Config) (authenticate : Receipt → Bool) :
    List Action → State → Prop where
  | initial : Run config authenticate [] {}
  | append {actions : List Action} {before after : State}
      (prior : Run config authenticate actions before)
      (action : Action)
      (accepted : step config authenticate before action = .ok after) :
      Run config authenticate (actions ++ [action]) after

/-- A successful signed exposure requires an acknowledged candidate equal to
    the policy's signed candidate. -/
theorem exposure_requires_ack (config : Config) (authenticate : Receipt → Bool)
    (before after : State)
    (accepted : step config authenticate before .expose = .ok after) :
    before.acknowledged.isSome = true ∧
    before.acknowledged = before.policy.signedHash := by
  simp [step] at accepted
  split at accepted
  · cases accepted
  · rename_i good
    constructor
    · cases ack : before.acknowledged with
      | none => exact False.elim (good (Or.inl ack))
      | some _ => rfl
    · by_cases matching : before.acknowledged = before.policy.signedHash
      · exact matching
      · exact False.elim (good (Or.inr matching))

/-- A successful driver transition never loses the log entry attesting to
    the currently acknowledged reservation. -/
theorem step_preserves_reservation_record
    (config : Config) (authenticate : Receipt → Bool)
    (before after : State) (action : Action)
    (recorded : ReservationRecorded before)
    (accepted : step config authenticate before action = .ok after) :
    ReservationRecorded after := by
  intro hash acknowledged
  cases action <;> dsimp [step] at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals cases accepted <;>
    simp_all [ReservationRecorded, List.mem_append]

/-- On every successful driver trace, any acknowledged reservation has a
    durable-reservation event already present in the effect log. -/
theorem run_reservation_record
    (config : Config) (authenticate : Receipt → Bool)
    (actions : List Action) (state : State)
    (run : Run config authenticate actions state) :
    ReservationRecorded state := by
  induction run with
  | initial => simp [ReservationRecorded]
  | append prior action accepted ih =>
    exact step_preserves_reservation_record config authenticate _ _ action ih accepted

/-- The exposure step appends exactly one signed-exposure event for the
    acknowledged candidate. -/
theorem exposure_appends_event
    (config : Config) (authenticate : Receipt → Bool)
    (before after : State)
    (accepted : step config authenticate before .expose = .ok after) :
    ∃ hash, before.acknowledged = some hash ∧
      after.effects = before.effects ++ [.signedExposure hash] := by
  have ack := exposure_requires_ack config authenticate before after accepted
  cases hopt : before.acknowledged with
  | none => simp [hopt] at ack
  | some hash =>
    refine ⟨hash, rfl, ?_⟩
    have signed : before.policy.signedHash = some hash := by
      simpa [hopt] using ack.2.symm
    have good : (!before.acknowledged.isSome ||
        before.acknowledged != before.policy.signedHash) = false := by
      simp [hopt, signed]
    simp [step, hopt, signed] at accepted
    cases policy : Tornado.Policy.stepAttempt before.policy .expose with
    | error error => simp [policy] at accepted
    | ok next =>
      simp [policy] at accepted
      cases accepted
      rfl

/-- In a reachable driver state, the newly appended signed exposure has a
    matching durable-reservation event in the *prior* log. This is an actual
    ordering statement over the abstract effect trace. -/
theorem run_exposure_has_prior_reservation
    (config : Config) (authenticate : Receipt → Bool)
    (actions : List Action) (before after : State)
    (run : Run config authenticate actions before)
    (accepted : step config authenticate before .expose = .ok after) :
    ∃ hash,
      Effect.durableReservation hash ∈ before.effects ∧
      after.effects = before.effects ++ [.signedExposure hash] := by
  obtain ⟨hash, acknowledged, exposure⟩ :=
    exposure_appends_event config authenticate before after accepted
  have recorded := run_reservation_record config authenticate actions before run
  exact ⟨hash, recorded hash acknowledged, exposure⟩

/-- The command skeleton can record confirmation only after its authenticator
    accepted the receipt for the selected chain and the strict decoded event
    bridge accepted that same receipt. The authenticator's correctness is an
    explicit external assumption, not an axiom in this theorem. -/
theorem confirmation_requires_authenticated_evidence
    (config : Config) (authenticate : Receipt → Bool)
    (before after : State) (receipt : Receipt)
    (accepted : step config authenticate before (.confirm receipt) = .ok after) :
    authenticate receipt = true ∧
    receipt.chainId = config.chainId ∧
    receipt.transactionHash ≠ "" ∧
    Tornado.Protocol.Events.directOutcome receipt.success receipt.logs
      config.entry config.withdrawal = .confirmed := by
  simp [step] at accepted
  split at accepted
  · cases accepted
  · rename_i good
    have authenticated : authenticate receipt = true := by
      cases h : authenticate receipt with
      | true => rfl
      | false => exact False.elim (good (Or.inl (Or.inl h)))
    have chain : receipt.chainId = config.chainId := by
      by_cases equal : receipt.chainId = config.chainId
      · exact equal
      · exact False.elim (good (Or.inl (Or.inr equal)))
    have transaction : receipt.transactionHash ≠ "" := by
      intro empty
      exact good (Or.inr empty)
    split at accepted
    · cases accepted
    · cases acknowledged : before.acknowledged with
      | none => simp [acknowledged] at accepted
      | some hash =>
        cases evidence : Tornado.Policy.EvidenceBridge.confirmDirect before.policy
            receipt.success receipt.logs config.entry config.withdrawal with
        | error error => simp [acknowledged, evidence] at accepted
        | ok policy =>
          have exactOutcome :=
            Tornado.Policy.EvidenceBridge.confirmDirect_sound before.policy policy
              receipt.success receipt.logs config.entry config.withdrawal evidence
          exact ⟨authenticated, chain, transaction, exactOutcome.1⟩

/-- An uncertain candidate cannot be reviewed or signed again, exposed again,
    or sent again through this driver, regardless of the caller-supplied ack. -/
theorem uncertain_blocks_new_operation
    (config : Config) (authenticate : Receipt → Bool)
    (state : State) (hash : String) (ack : DurableAck)
    (unknown : state.policy.phase = .unknown) :
    (step config authenticate state (.review hash)).isOk = false ∧
    (step config authenticate state (.sign hash)).isOk = false ∧
    (step config authenticate state (.reserve ack)).isOk = false ∧
    (step config authenticate state .expose).isOk = false ∧
    (step config authenticate state .send).isOk = false := by
  have freshFalse : (Tornado.Policy.AttemptPhase.unknown == .fresh) = false := by decide
  have approvedFalse : (Tornado.Policy.AttemptPhase.unknown == .approved) = false := by decide
  have signedFalse : (Tornado.Policy.AttemptPhase.unknown == .signed) = false := by decide
  have reservedFalse : (Tornado.Policy.AttemptPhase.unknown == .reserved) = false := by decide
  have reviewFail : Tornado.Policy.stepAttempt state.policy (.approve hash) =
      .error "An unresolved attempt blocks approval." := by
    simp [Tornado.Policy.stepAttempt, unknown, freshFalse]
  have signFail : Tornado.Policy.stepAttempt state.policy (.sign hash) =
      .error "The signed payload differs from the approved hash." := by
    simp [Tornado.Policy.stepAttempt, unknown, approvedFalse]
  have reserveFail : Tornado.Policy.stepAttempt state.policy .reserve =
      .error "The candidate is not ready for reservation." := by
    simp [Tornado.Policy.stepAttempt, unknown, signedFalse]
  have exposeFail : Tornado.Policy.stepAttempt state.policy .expose =
      .error "Exposure requires a matching reservation." := by
    simp [Tornado.Policy.stepAttempt, unknown, reservedFalse]
  have sendFail : Tornado.Policy.stepAttempt state.policy .send =
      .error "Submission requires a matching reservation and no earlier send." := by
    simp [Tornado.Policy.stepAttempt, unknown]
  simp [step, reviewFail, signFail, reserveFail, exposeFail, sendFail, Except.isOk]
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals decide

namespace Batch

/-- Every acknowledged note has a prior durable-reservation event. -/
def ReservationsRecorded (state : State) : Prop :=
  ∀ note, note ∈ state.acknowledged →
    Effect.durableReservation note ∈ state.effects

/-- A reachable batch has either not selected notes yet, or has selected
    exactly the configured withdrawal nullifiers. -/
def SelectionMatchesConfig (config : Config) (state : State) : Prop :=
  state.policy.selected = [] ∨
    state.policy.selected =
      Tornado.Policy.EvidenceBridge.withdrawalTexts config.withdrawals

inductive Run (config : Config) (authenticate : Receipt → Bool) :
    List Action → State → Prop where
  | initial : Run config authenticate [] {}
  | append {actions : List Action} {before after : State}
      (prior : Run config authenticate actions before)
      (action : Action)
      (accepted : step config authenticate before action = .ok after) :
      Run config authenticate (actions ++ [action]) after

/-- Driver transitions cannot change the selected notes except at the
    configured preparation step. -/
theorem step_preserves_config_selection
    (config : Config) (authenticate : Receipt → Bool)
    (before after : State) (action : Action)
    (matching : SelectionMatchesConfig config before)
    (accepted : step config authenticate before action = .ok after) :
    SelectionMatchesConfig config after := by
  cases action <;> dsimp [step] at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals cases accepted <;>
    simp_all [SelectionMatchesConfig, Tornado.Policy.EvidenceBridge.withdrawalTexts]
  all_goals simp_all [Tornado.Policy.Batch.step,
    Tornado.Policy.EvidenceBridge.confirmBatch]
  all_goals repeat (split at * <;> simp_all)
  all_goals subst_vars
  all_goals try simp_all
  all_goals grind

/-- In every driver trace from the empty state, the note selection stays
    tied to the expected withdrawal list in the command configuration. -/
theorem run_selection_matches_config
    (config : Config) (authenticate : Receipt → Bool)
    (actions : List Action) (state : State)
    (run : Run config authenticate actions state) :
    SelectionMatchesConfig config state := by
  induction run with
  | initial => exact Or.inl rfl
  | append prior action accepted ih =>
    exact step_preserves_config_selection config authenticate _ _ action ih accepted

/-- No successful batch driver transition can erase an accepted note's
    durable-reservation log entry. -/
theorem step_preserves_reservations_recorded
    (config : Config) (authenticate : Receipt → Bool)
    (before after : State) (action : Action)
    (recorded : ReservationsRecorded before)
    (accepted : step config authenticate before action = .ok after) :
    ReservationsRecorded after := by
  intro note member
  cases action <;> dsimp [step] at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals try split at accepted
  all_goals cases accepted <;>
    simp_all [ReservationsRecorded, List.mem_append]
  all_goals
    cases member with
    | inl earlier => exact Or.inl (recorded note earlier)
    | inr current => exact Or.inr current

/-- Each accepted acknowledgment in any reachable batch state is backed by
    a reservation event in the earlier effect log. -/
theorem run_reservations_recorded
    (config : Config) (authenticate : Receipt → Bool)
    (actions : List Action) (state : State)
    (run : Run config authenticate actions state) :
    ReservationsRecorded state := by
  induction run with
  | initial => simp [ReservationsRecorded]
  | append prior action accepted ih =>
    exact step_preserves_reservations_recorded config authenticate _ _ action ih accepted

/-- The batch driver cannot expose until every selected note appears in its
    acknowledged-reservation list. -/
theorem exposure_requires_all_ack
    (config : Config) (authenticate : Receipt → Bool)
    (before after : State)
    (accepted : step config authenticate before .expose = .ok after) :
    before.policy.selected.all before.acknowledged.contains = true := by
  simp [step] at accepted
  split at accepted
  · cases accepted
  · rename_i good
    have covered : ∀ note, note ∈ before.policy.selected →
        note ∈ before.acknowledged := by
      intro note selected
      by_cases acknowledged : note ∈ before.acknowledged
      · exact acknowledged
      · exact False.elim (good (Or.inl ⟨note, selected, acknowledged⟩))
    simpa [List.all_eq_true, List.contains_iff_mem] using covered

/-- A successful batch exposure appends one effect carrying the signed hash. -/
theorem exposure_appends_event
    (config : Config) (authenticate : Receipt → Bool)
    (before after : State)
    (accepted : step config authenticate before .expose = .ok after) :
    ∃ hash, before.policy.signedHash = some hash ∧
      after.effects = before.effects ++ [.signedExposure hash] := by
  simp [step] at accepted
  split at accepted
  · cases accepted
  · cases signed : before.policy.signedHash with
    | none => simp [signed] at accepted
    | some hash =>
      cases policy : Tornado.Policy.Batch.step before.policy .expose with
      | error error => simp [signed, policy] at accepted
      | ok next =>
        simp [signed, policy] at accepted
        cases accepted
        exact ⟨hash, rfl, rfl⟩

/-- Every selected note's durable-reservation event is in the prefix before
    the shared signed-exposure event of a reachable batch run. -/
theorem run_exposure_has_all_prior_reservations
    (config : Config) (authenticate : Receipt → Bool)
    (actions : List Action) (before after : State)
    (run : Run config authenticate actions before)
    (accepted : step config authenticate before .expose = .ok after) :
    ∃ hash,
      (∀ note, note ∈ before.policy.selected →
        Effect.durableReservation note ∈ before.effects) ∧
      after.effects = before.effects ++ [.signedExposure hash] := by
  obtain ⟨hash, _, exposure⟩ :=
    exposure_appends_event config authenticate before after accepted
  have acknowledged := exposure_requires_all_ack config authenticate before after accepted
  have recorded := run_reservations_recorded config authenticate actions before run
  have covered : ∀ note, note ∈ before.policy.selected →
      note ∈ before.acknowledged := by
    simpa [List.all_eq_true, List.contains_iff_mem] using acknowledged
  exact ⟨hash, (fun note member => recorded note (covered note member)), exposure⟩

/-- A successful batch confirmation passes the supplied receipt authenticator,
    matches the configured chain, and contains exact decoded evidence for the
    configured batch. The authenticator's truthfulness is external. -/
theorem confirmation_requires_authenticated_evidence
    (config : Config) (authenticate : Receipt → Bool)
    (before after : State) (receipt : Receipt)
    (accepted : step config authenticate before (.confirm receipt) = .ok after) :
    authenticate receipt = true ∧
    receipt.chainId = config.chainId ∧
    receipt.transactionHash ≠ "" ∧
    Tornado.Protocol.Events.batchOutcome receipt.success receipt.logs
      config.entry config.withdrawals = .confirmed ∧
    before.policy.selected =
      Tornado.Policy.EvidenceBridge.withdrawalTexts config.withdrawals := by
  simp [step] at accepted
  split at accepted
  · cases accepted
  · rename_i good
    have authenticated : authenticate receipt = true := by
      cases h : authenticate receipt with
      | true => rfl
      | false => exact False.elim (good (Or.inl (Or.inl h)))
    have chain : receipt.chainId = config.chainId := by
      by_cases equal : receipt.chainId = config.chainId
      · exact equal
      · exact False.elim (good (Or.inl (Or.inr equal)))
    have transaction : receipt.transactionHash ≠ "" := by
      intro empty
      exact good (Or.inr empty)
    split at accepted
    · cases accepted
    · cases signed : before.policy.signedHash with
      | none => simp [signed] at accepted
      | some hash =>
        cases evidence : Tornado.Policy.EvidenceBridge.confirmBatch before.policy
            receipt.success receipt.logs config.entry config.withdrawals with
        | error error => simp [signed, evidence] at accepted
        | ok policy =>
          have exactOutcome :=
            Tornado.Policy.EvidenceBridge.confirmBatch_sound before.policy policy
              receipt.success receipt.logs config.entry config.withdrawals evidence
          exact ⟨authenticated, chain, transaction, exactOutcome.1, exactOutcome.2.1⟩

/-- An uncertain batch cannot be prepared, re-signed, re-reserved, exposed,
    or sent again through this driver, regardless of the caller-supplied ack. -/
theorem uncertain_blocks_new_operation
    (config : Config) (authenticate : Receipt → Bool)
    (state : State) (notes : List String) (hash : String) (ack : DurableAck)
    (unknown : state.policy.phase = .unknown) :
    (step config authenticate state (.prepare notes hash)).isOk = false ∧
    (step config authenticate state (.sign hash)).isOk = false ∧
    (step config authenticate state (.reserve ack)).isOk = false ∧
    (step config authenticate state .expose).isOk = false ∧
    (step config authenticate state .send).isOk = false := by
  have freshFalse : (Tornado.Policy.Batch.Phase.unknown == .fresh) = false := by decide
  have reviewedFalse : (Tornado.Policy.Batch.Phase.unknown == .reviewed) = false := by decide
  have signedFalse : (Tornado.Policy.Batch.Phase.unknown == .signed) = false := by decide
  have reservingFalse : (Tornado.Policy.Batch.Phase.unknown == .reserving) = false := by decide
  have exposedFalse : (Tornado.Policy.Batch.Phase.unknown == .exposed) = false := by decide
  have prepareFail : Tornado.Policy.Batch.step state.policy (.prepare notes hash) =
      .error "A batch must select unique notes and an approved payload." := by
    simp [Tornado.Policy.Batch.step, unknown, freshFalse]
  have signFail : Tornado.Policy.Batch.step state.policy (.sign hash) =
      .error "The batch signature differs from the reviewed payload." := by
    simp [Tornado.Policy.Batch.step, unknown, reviewedFalse]
  have reserveFail : Tornado.Policy.Batch.step state.policy (.reserveNote ack.nullifier) =
      .error "The note is not a fresh reservation for this signed batch." := by
    simp [Tornado.Policy.Batch.step, unknown, signedFalse, reservingFalse]
  have exposeFail : Tornado.Policy.Batch.step state.policy .expose =
      .error "Every selected note must be reserved before exposure." := by
    simp [Tornado.Policy.Batch.step, unknown, reservingFalse]
  have sendFail : Tornado.Policy.Batch.step state.policy .send =
      .error "A reserved batch can be sent only once." := by
    simp [Tornado.Policy.Batch.step, unknown, exposedFalse]
  simp [step, prepareFail, signFail, reserveFail, exposeFail, sendFail, Except.isOk]
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals try split
  all_goals decide

end Batch

end Tornado.Spec.Effects

#print axioms Tornado.Spec.Effects.exposure_requires_ack
#print axioms Tornado.Spec.Effects.step_preserves_reservation_record
#print axioms Tornado.Spec.Effects.run_reservation_record
#print axioms Tornado.Spec.Effects.exposure_appends_event
#print axioms Tornado.Spec.Effects.run_exposure_has_prior_reservation
#print axioms Tornado.Spec.Effects.confirmation_requires_authenticated_evidence
#print axioms Tornado.Spec.Effects.uncertain_blocks_new_operation
#print axioms Tornado.Spec.Effects.Batch.step_preserves_reservations_recorded
#print axioms Tornado.Spec.Effects.Batch.run_reservations_recorded
#print axioms Tornado.Spec.Effects.Batch.step_preserves_config_selection
#print axioms Tornado.Spec.Effects.Batch.run_selection_matches_config
#print axioms Tornado.Spec.Effects.Batch.exposure_requires_all_ack
#print axioms Tornado.Spec.Effects.Batch.exposure_appends_event
#print axioms Tornado.Spec.Effects.Batch.run_exposure_has_all_prior_reservations
#print axioms Tornado.Spec.Effects.Batch.confirmation_requires_authenticated_evidence
#print axioms Tornado.Spec.Effects.Batch.uncertain_blocks_new_operation
