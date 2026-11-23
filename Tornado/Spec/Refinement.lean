import Tornado.Spec.Attempt
import Tornado.PolicyProofs
import Tornado.Policy.BatchProofs
import Tornado.Policy.EvidenceBridge

namespace Tornado.Spec

private theorem direct_phase_fresh_of_beq (phase : Tornado.Policy.AttemptPhase)
    (h : (phase == .fresh) = true) : phase = .fresh := by
  cases phase <;> cases h <;> rfl

/-- Every successful one-note transition preserves the independent send cap. -/
theorem direct_step_send_cap (before after : Tornado.Policy.Attempt)
    (action : Tornado.Policy.AttemptAction)
    (cap : AtMostOneSend before.sends)
    (transition : Tornado.Policy.stepAttempt before action = .ok after) :
    AtMostOneSend after.sends := by
  cases action <;> dsimp [Tornado.Policy.stepAttempt] at transition
  all_goals try split at transition
  all_goals try split at transition
  all_goals cases transition <;> simp_all [AtMostOneSend]

/-- The same cap is invariant for a whole successful one-note run. -/
theorem direct_run_send_cap (actions : List Tornado.Policy.AttemptAction)
    (state : Tornado.Policy.Attempt) (run : DirectRun actions state) :
    AtMostOneSend state.sends := by
  induction run with
  | initial => simp [AtMostOneSend]
  | append prior action transition ih =>
    exact direct_step_send_cap _ _ action ih transition

/-- Even a forged exposed state with one recorded send cannot pass the native
    send transition a second time. The run invariant separately bounds the
    count in reachable states. -/
theorem direct_second_send_rejected (state : Tornado.Policy.Attempt)
    (sent : state.sends = 1) :
    Tornado.Policy.stepAttempt state .send =
      .error "Submission requires a matching reservation and no earlier send." := by
  cases phase : state.phase <;>
    simp [Tornado.Policy.stepAttempt, phase, sent]

/-- The one-note reviewed-hash invariant survives any successful native
    transition, independently of the trace length. -/
theorem direct_step_review_invariant (before after : Tornado.Policy.Attempt)
    (action : Tornado.Policy.AttemptAction)
    (invariant : DirectReviewInvariant before)
    (transition : Tornado.Policy.stepAttempt before action = .ok after) :
    DirectReviewInvariant after := by
  cases action <;> dsimp [Tornado.Policy.stepAttempt] at transition
  all_goals try split at transition
  all_goals try split at transition
  all_goals cases transition <;> simp_all [DirectReviewInvariant]
  all_goals
    intro hsome
    have hfresh : before.phase = .fresh := by
      apply direct_phase_fresh_of_beq
      apply And.left
      assumption
    have hsigned := invariant.1 hfresh
    simp [hsigned] at hsome

/-- Every reachable one-note state keeps any signed hash bound to review. -/
theorem direct_run_review_invariant (actions : List Tornado.Policy.AttemptAction)
    (state : Tornado.Policy.Attempt) (run : DirectRun actions state) :
    DirectReviewInvariant state := by
  induction run with
  | initial => simp [DirectReviewInvariant]
  | append prior action transition ih =>
    exact direct_step_review_invariant _ _ action ih transition

/-- In a reachable one-note run, exposure is impossible unless one identical
    operation hash was reviewed, signed and reserved. -/
theorem direct_exposure_refines_spec
    (actions : List Tornado.Policy.AttemptAction)
    (before after : Tornado.Policy.Attempt)
    (run : DirectRun actions before)
    (transition : Tornado.Policy.stepAttempt before .expose = .ok after) :
    DirectExposureSpec before := by
  have review := direct_run_review_invariant actions before run
  obtain ⟨matching, present⟩ :=
    Tornado.Policy.exposure_requires_matching_reservation before after transition
  cases reserved : before.reservedHash with
  | none => simp [reserved] at present
  | some hash =>
    have hsigned : before.signedHash = some hash := by
      simpa [reserved] using matching.symm
    have hsignedPresent : before.signedHash.isSome := by simp [hsigned]
    have hreviewed : before.reviewedHash = some hash := by
      rw [review.2 hsignedPresent, hsigned]
    exact ⟨hash, hreviewed, hsigned, reserved⟩

/-- Every successful batch transition preserves the independent send cap. -/
theorem batch_step_send_cap (before after : Tornado.Policy.Batch.Attempt)
    (action : Tornado.Policy.Batch.Action)
    (cap : AtMostOneSend before.sends)
    (transition : Tornado.Policy.Batch.step before action = .ok after) :
    AtMostOneSend after.sends := by
  cases action <;> dsimp [Tornado.Policy.Batch.step] at transition
  all_goals try split at transition
  all_goals try split at transition
  all_goals cases transition <;> simp_all [AtMostOneSend]

/-- The batch send cap holds for all states reached from the empty batch. -/
theorem batch_run_send_cap (actions : List Tornado.Policy.Batch.Action)
    (state : Tornado.Policy.Batch.Attempt) (run : BatchRun actions state) :
    AtMostOneSend state.sends := by
  induction run with
  | initial => simp [AtMostOneSend]
  | append prior action transition ih =>
    exact batch_step_send_cap _ _ action ih transition

/-- The batch gate rejects a second send even if the caller presents an
    otherwise well-formed exposed state. -/
theorem batch_second_send_rejected (state : Tornado.Policy.Batch.Attempt)
    (sent : state.sends = 1) :
    Tornado.Policy.Batch.step state .send =
      .error "A reserved batch can be sent only once." := by
  simp [Tornado.Policy.Batch.step, sent]

/-- Only preparation introduces a selection, and it introduces one that
    passed the native nonempty/unique/size guard. -/
theorem batch_step_selection_invariant (before after : Tornado.Policy.Batch.Attempt)
    (action : Tornado.Policy.Batch.Action)
    (invariant : BatchSelectionInvariant before)
    (transition : Tornado.Policy.Batch.step before action = .ok after) :
    BatchSelectionInvariant after := by
  cases action <;> dsimp [Tornado.Policy.Batch.step] at transition
  all_goals try split at transition
  all_goals try split at transition
  all_goals cases transition <;> simp_all [BatchSelectionInvariant]
  all_goals
    apply invariant.2
    intro hfresh
    have hreviewed : (Tornado.Policy.Batch.Phase.fresh == .reviewed) = false := by decide
    have hsigned : (Tornado.Policy.Batch.Phase.fresh == .signed) = false := by decide
    have hreserving : (Tornado.Policy.Batch.Phase.fresh == .reserving) = false := by decide
    have hexposed : (Tornado.Policy.Batch.Phase.fresh == .exposed) = false := by decide
    have hsubmitted : (Tornado.Policy.Batch.Phase.fresh == .submitted) = false := by decide
    have hunknown : (Tornado.Policy.Batch.Phase.fresh == .unknown) = false := by decide
    simp_all

/-- Selection validity is a whole-run invariant of the native batch policy. -/
theorem batch_run_selection_invariant (actions : List Tornado.Policy.Batch.Action)
    (state : Tornado.Policy.Batch.Attempt) (run : BatchRun actions state) :
    BatchSelectionInvariant state := by
  induction run with
  | initial => simp [BatchSelectionInvariant]
  | append prior action transition ih =>
    exact batch_step_selection_invariant _ _ action ih transition

/-- Along a reachable batch run, successful exposure meets the independent
    spec: a nonempty selection, every selected note reserved, and one hash
    shared by review and signature. -/
theorem batch_exposure_refines_spec
    (actions : List Tornado.Policy.Batch.Action)
    (before after : Tornado.Policy.Batch.Attempt)
    (run : BatchRun actions before)
    (transition : Tornado.Policy.Batch.step before .expose = .ok after) :
    BatchExposureSpec before := by
  have selection := batch_run_selection_invariant actions before run
  have nonfresh : before.phase ≠ .fresh := by
    intro fresh
    have hfalse : (Tornado.Policy.Batch.Phase.fresh == .reserving) = false := by decide
    simp [Tornado.Policy.Batch.step, fresh, hfalse] at transition
  have valid := selection.2 nonfresh
  have nonempty : before.selected ≠ [] := by
    intro empty
    simp [Tornado.Policy.Batch.validSelection, empty] at valid
  have reserved := Tornado.Policy.Batch.exposure_requires_all_reserved before after transition
  have covered : ∀ note, note ∈ before.selected → note ∈ before.reserved := by
    simpa [Tornado.Policy.Batch.allReserved, List.all_eq_true,
      List.contains_iff_mem] using reserved
  dsimp [Tornado.Policy.Batch.step] at transition
  split at transition
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    have equal := guard.1.2
    have present := guard.2
    cases signed : before.signedHash with
    | none => simp [signed] at present
    | some hash =>
      have reviewed : before.reviewedHash = some hash := by
        rw [equal, signed]
      exact ⟨nonempty, covered, hash, reviewed, signed⟩
  · contradiction

/-- An accepted native one-note evidence bridge extends a successful run
    only when the independent receipt/event acceptance specification holds. -/
theorem direct_bridge_refines_spec
    (actions : List Tornado.Policy.AttemptAction)
    (before after : Tornado.Policy.Attempt)
    (receiptSuccess : Bool)
    (logs : List Tornado.Protocol.Events.Log)
    (entry : Tornado.Protocol.Events.ExpectedEntry)
    (withdrawal : Tornado.Protocol.Events.ExpectedWithdrawal)
    (run : DirectRun actions before)
    (accepted : Tornado.Policy.EvidenceBridge.confirmDirect before receiptSuccess logs
      entry withdrawal = .ok after) :
    DirectConfirmationSpec receiptSuccess logs entry withdrawal ∧
    DirectRun (actions ++ [.confirm
      (Tornado.Policy.EvidenceBridge.directEvidence receiptSuccess logs entry withdrawal)]) after := by
  obtain ⟨_, _, transition, receipt, entryEvent, withdrawalEvent⟩ :=
    Tornado.Policy.EvidenceBridge.confirmDirect_sound before after receiptSuccess logs
      entry withdrawal accepted
  exact ⟨⟨receipt, entryEvent, withdrawalEvent⟩,
    DirectRun.append run _ transition⟩

/-- The batch bridge requires exact selected-note coverage and extends the
    batch run through the same native confirmation transition it checked. -/
theorem batch_bridge_refines_spec
    (actions : List Tornado.Policy.Batch.Action)
    (before after : Tornado.Policy.Batch.Attempt)
    (receiptSuccess : Bool)
    (logs : List Tornado.Protocol.Events.Log)
    (entry : Tornado.Protocol.Events.ExpectedEntry)
    (withdrawals : List Tornado.Protocol.Events.ExpectedWithdrawal)
    (run : BatchRun actions before)
    (accepted : Tornado.Policy.EvidenceBridge.confirmBatch before receiptSuccess logs
      entry withdrawals = .ok after) :
    BatchConfirmationSpec receiptSuccess logs entry withdrawals ∧
    before.selected = Tornado.Policy.EvidenceBridge.withdrawalTexts withdrawals ∧
    BatchRun (actions ++ [.confirm
      (Tornado.Policy.EvidenceBridge.batchEvidence receiptSuccess logs entry withdrawals)]) after := by
  obtain ⟨outcome, selected, _, transition, receipt, entryEvent, allEvents⟩ :=
    Tornado.Policy.EvidenceBridge.confirmBatch_sound before after receiptSuccess logs
      entry withdrawals accepted
  have nonempty : withdrawals ≠ [] := by
    intro empty
    subst withdrawals
    simp [Tornado.Protocol.Events.batchOutcome] at outcome
    split at outcome <;> contradiction
  have covered : ∀ withdrawal, withdrawal ∈ withdrawals →
      Tornado.Protocol.Events.hasWithdrawal logs withdrawal = true := by
    simpa [List.all_eq_true] using allEvents
  exact ⟨⟨receipt, entryEvent, nonempty, covered⟩, selected,
    BatchRun.append run _ transition⟩

end Tornado.Spec

#print axioms Tornado.Spec.direct_step_send_cap
#print axioms Tornado.Spec.direct_run_send_cap
#print axioms Tornado.Spec.direct_second_send_rejected
#print axioms Tornado.Spec.direct_step_review_invariant
#print axioms Tornado.Spec.direct_run_review_invariant
#print axioms Tornado.Spec.direct_exposure_refines_spec
#print axioms Tornado.Spec.batch_step_send_cap
#print axioms Tornado.Spec.batch_run_send_cap
#print axioms Tornado.Spec.batch_second_send_rejected
#print axioms Tornado.Spec.batch_step_selection_invariant
#print axioms Tornado.Spec.batch_run_selection_invariant
#print axioms Tornado.Spec.batch_exposure_refines_spec
#print axioms Tornado.Spec.direct_bridge_refines_spec
#print axioms Tornado.Spec.batch_bridge_refines_spec
#print axioms Tornado.Spec.direct_phase_fresh_of_beq
