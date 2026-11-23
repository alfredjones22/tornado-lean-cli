import Tornado.Cli.WithdrawalSend

/-! Properties of the exact next-command/respond machine interpreted by
WithdrawalSend.executeWith. Callback acknowledgments are IO contracts, not
proofs of disk persistence, network truth or signer security. -/

namespace Tornado.Spec.WithdrawalDriver

open Lean Tornado.Protocol Tornado.Protocol.UserOperation08
open Tornado.Runtime
open Tornado.Runtime.WithdrawalDriver

theorem prepared_review_is_actual_builder (review : Tornado.Cli.WithdrawalSend.Review)
    (prepared : Tornado.Cli.WithdrawalSend.PreparedReview review) :
    Tornado.Cli.WithdrawalSend.build review = .ok prepared.operation := prepared.built

theorem finalized_changes_only_signature {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (payload : FinalPayload reviewed) :
    payload.operation = { unsigned with signature := payload.signed.signature } ∧
    payload.signed.owner = reviewed.owner :=
  ⟨payload.operationExact, payload.ownerBound⟩

theorem finalized_binds_full_authorized_bytes {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (payload : FinalPayload reviewed) :
    Bundler.withAuthorization reviewed.chainId payload.operation payload.signed.authorization = .ok payload.json ∧
    payload.bytes = payload.json.compress.toUTF8 ∧
    authorizationAllowed reviewed.flow reviewed.chainId payload.signed.authorization = true ∧
    userOperationHash reviewed.chainId Bundler.entryPoint payload.operation = .ok reviewed.hash :=
  ⟨payload.jsonBound, payload.bytesBound, payload.authorizationBound, payload.hashBound⟩

theorem response_records_dispatched_command {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (command : Command reviewed) (reply : Reply)
    (dispatched : next state = some command) :
    ∃ accepted, (respond state reply).history =
      state.history ++ [⟨command.kind, accepted⟩] := by
  simp only [respond, dispatched]
  exact ⟨(decideResponse state command reply).accepted, rfl⟩

theorem next_sign_requires_review_and_revalidation {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (dispatched : next state = some .sign) :
    acknowledged state .approve = true ∧ acknowledged state .revalidate = true ∧
      called state .sign = false ∧ locked state = false := by
  cases phase : state.phase <;> cases payload : state.payload <;>
    simp [next, phase, payload] at dispatched
  all_goals repeat first | split at dispatched | contradiction
  all_goals simp_all

theorem next_exposure_mark_requires_reservation {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (payload : FinalPayload reviewed)
    (dispatched : next state = some (.markExposed payload)) :
    acknowledged state .reserve = true ∧ called state .markExposed = false := by
  cases phase : state.phase <;> cases present : state.payload <;>
    simp [next, phase, present] at dispatched
  all_goals repeat first | split at dispatched | contradiction
  all_goals simp_all

theorem next_simulation_requires_prior_acks {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (payload : FinalPayload reviewed)
    (dispatched : next state = some (.simulate payload)) :
    readyForExposure state = true ∧ called state .simulate = false ∧ called state .send = false := by
  cases phase : state.phase <;> cases present : state.payload <;>
    simp [next, phase, present] at dispatched
  all_goals repeat first | split at dispatched | contradiction
  all_goals simp_all

theorem next_send_requires_prior_acks {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (payload : FinalPayload reviewed)
    (dispatched : next state = some (.send payload)) :
    readyForExposure state = true ∧ called state .send = false ∧
      (reviewed.flow == .direct || acknowledged state .simulate) = true := by
  cases phase : state.phase <;> cases present : state.payload <;>
    simp [next, phase, present] at dispatched
  all_goals repeat first | split at dispatched | contradiction
  all_goals simp_all

theorem exposure_ack_fields {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (ready : readyForExposure state = true) :
    acknowledged state .approve = true ∧ acknowledged state .revalidate = true ∧
    acknowledged state .sign = true ∧ acknowledged state .reserve = true ∧
    acknowledged state .markExposed = true := by
  simpa [readyForExposure, Bool.and_eq_true, and_assoc] using ready

theorem failed_reservation_blocks_exposure {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (payload : FinalPayload reviewed)
    (dispatched : next state = some (.reserve payload)) :
    (respond state .failed).phase = .blocked ∧ next (respond state .failed) = none := by
  have stopped : (respond state .failed).phase = .blocked := by
    rw [respond, dispatched]
    rfl
  exact ⟨stopped, by simp [next, stopped]⟩

theorem failed_exposure_mark_blocks_network {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (payload : FinalPayload reviewed)
    (dispatched : next state = some (.markExposed payload)) :
    (respond state .failed).phase = .blocked ∧ next (respond state .failed) = none := by
  have stopped : (respond state .failed).phase = .blocked := by
    rw [respond, dispatched]
    rfl
  exact ⟨stopped, by simp [next, stopped]⟩

theorem lost_send_reply_keeps_unknown_path {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (payload : FinalPayload reviewed)
    (dispatched : next state = some (.send payload)) :
    (respond state .failed).phase = .markUnknown ∧
    called (respond state .failed) .send = true := by
  simp [respond, dispatched, decideResponse, called, Command.kind,
    show (Kind.send == Kind.send) = true from rfl]

theorem rejected_simulation_keeps_unknown_path {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (payload : FinalPayload reviewed)
    (dispatched : next state = some (.simulate payload)) :
    (respond state (.simulation false)).phase = .markUnknown := by
  simp [respond, dispatched, decideResponse]

theorem unknown_phase_is_terminal {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (unknown : state.phase = .unknown) : next state = none := by
  simp [next, unknown]

theorem prior_exposure_blocks_new_signature {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (exposed : locked state = true) : next state ≠ some .sign := by
  intro dispatched
  have bound := next_sign_requires_review_and_revalidation reviewed state dispatched
  simp [exposed] at bound

theorem prior_send_blocks_second_send {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (payload : FinalPayload reviewed) (sent : called state .send = true) :
    next state ≠ some (.send payload) := by
  intro dispatched
  have bound := next_send_requires_prior_acks reviewed state payload dispatched
  simp [sent] at bound

private theorem kind_beq_eq (left right : Kind) : (left == right) = true ↔ left = right := by
  cases left <;> cases right <;> decide

theorem acknowledged_event_is_in_prior_trace {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed) (kind : Kind)
    (ack : acknowledged state kind = true) : (⟨kind, true⟩ : Observation) ∈ state.history := by
  obtain ⟨event, member, accepted⟩ := List.any_eq_true.mp ack
  have fields : (event.kind == kind) = true ∧ event.accepted = true := by
    simpa only [Bool.and_eq_true] using accepted
  have same := (kind_beq_eq event.kind kind).mp fields.1
  have equal : event = (⟨kind, true⟩ : Observation) := by
    cases event
    simp_all
  simpa [equal] using member

theorem dispatched_network_has_prior_successes {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (_reachable : Reachable reviewed state) (payload : FinalPayload reviewed)
    (network : next state = some (.simulate payload) ∨ next state = some (.send payload)) :
    (⟨.approve, true⟩ : Observation) ∈ state.history ∧
    (⟨.revalidate, true⟩ : Observation) ∈ state.history ∧
    (⟨.sign, true⟩ : Observation) ∈ state.history ∧
    (⟨.reserve, true⟩ : Observation) ∈ state.history ∧
    (⟨.markExposed, true⟩ : Observation) ∈ state.history := by
  have ready : readyForExposure state = true := by
    cases network with
    | inl simulation => exact (next_simulation_requires_prior_acks reviewed state payload simulation).1
    | inr send => exact (next_send_requires_prior_acks reviewed state payload send).1
  obtain ⟨approve, revalidate, sign, reserve, exposed⟩ := exposure_ack_fields reviewed state ready
  exact ⟨acknowledged_event_is_in_prior_trace reviewed state _ approve,
    acknowledged_event_is_in_prior_trace reviewed state _ revalidate,
    acknowledged_event_is_in_prior_trace reviewed state _ sign,
    acknowledged_event_is_in_prior_trace reviewed state _ reserve,
    acknowledged_event_is_in_prior_trace reviewed state _ exposed⟩

def invocations {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (state : State reviewed) (kind : Kind) : Nat :=
  state.history.countP (fun event => event.kind == kind)

private theorem absent_call_count_zero {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed) (kind : Kind)
    (absent : called state kind = false) : invocations state kind = 0 := by
  apply List.countP_eq_zero.mpr
  exact List.any_eq_false.mp absent

private theorem unique_dispatched_command_has_no_prior_call {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed) (command : Command reviewed)
    (dispatched : next state = some command)
    (unique : command.kind = .sign ∨ command.kind = .send ∨ command.kind = .simulate) :
    called state command.kind = false := by
  cases command with
  | sign => exact (next_sign_requires_review_and_revalidation reviewed state dispatched).2.2.1
  | send payload => exact (next_send_requires_prior_acks reviewed state payload dispatched).2.1
  | simulate payload => exact (next_simulation_requires_prior_acks reviewed state payload dispatched).2.1
  | _ => simp [Command.kind] at unique

/-- Counts completed callback invocations, including failed/lost replies,
not only successful transitions or manually incremented policy counters. -/
theorem reachable_callback_count_at_most_one {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed) (kind : Kind)
    (unique : kind = .sign ∨ kind = .send ∨ kind = .simulate)
    (reachable : Reachable reviewed state) : invocations state kind ≤ 1 := by
  induction reachable with
  | initial => simp [invocations, initial]
  | @response before prior reply ih =>
    cases dispatched : next before with
    | none => simpa [respond, dispatched] using ih
    | some command =>
      obtain ⟨accepted, history⟩ := response_records_dispatched_command reviewed before command reply dispatched
      change (respond before reply).history.countP (fun event => event.kind == kind) ≤ 1
      rw [history, List.countP_append, List.countP_singleton]
      by_cases same : command.kind = kind
      · have absent := unique_dispatched_command_has_no_prior_call reviewed before command dispatched (by simpa [same] using unique)
        have zero := absent_call_count_zero reviewed before kind (by simpa [same] using absent)
        have equal : (command.kind == kind) = true := (kind_beq_eq _ _).mpr same
        simpa [equal, invocations] using (show invocations before kind + 1 ≤ 1 by omega)
      · have different : (command.kind == kind) = false := by
          cases compare : command.kind == kind with
          | false => rfl
          | true => exact False.elim (same ((kind_beq_eq _ _).mp compare))
        simpa [different, invocations] using ih

theorem reachable_one_signature_and_submission {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (reachable : Reachable reviewed state) :
    invocations state .sign ≤ 1 ∧ invocations state .send ≤ 1 ∧ invocations state .simulate ≤ 1 :=
  ⟨reachable_callback_count_at_most_one reviewed state _ (Or.inl rfl) reachable,
    reachable_callback_count_at_most_one reviewed state _ (Or.inr (Or.inl rfl)) reachable,
    reachable_callback_count_at_most_one reviewed state _ (Or.inr (Or.inr rfl)) reachable⟩

theorem returned_report_has_global_callback_cap {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (report : Report reviewed) :
    invocations report.state .sign ≤ 1 ∧ invocations report.state .send ≤ 1 ∧
      invocations report.state .simulate ≤ 1 :=
  reachable_one_signature_and_submission reviewed report.state report.reachable

private theorem acknowledged_implies_called {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed) (kind : Kind)
    (ack : acknowledged state kind = true) : called state kind = true := by
  have member := acknowledged_event_is_in_prior_trace reviewed state kind ack
  apply List.any_eq_true.mpr
  exact ⟨⟨kind, true⟩, member, (kind_beq_eq kind kind).mpr rfl⟩

private theorem non_sign_decision_preserves_payload {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed)
    (command : Command reviewed) (reply : Reply) (notSign : command.kind ≠ .sign) :
    (decideResponse state command reply).payload = state.payload := by
  cases command <;> cases reply <;> simp_all [Command.kind]
  all_goals simp [decideResponse]
  all_goals repeat first | split | rfl

/-- Once a signature was accepted, later reservation, exposure and outcome
responses retain that same immutable full payload, including authorization. -/
theorem signed_payload_is_stable {unsigned : UserOperation}
    (reviewed : ReviewedOperation unsigned) (state : State reviewed) (reply : Reply)
    (signed : acknowledged state .sign = true) :
    (respond state reply).payload = state.payload := by
  cases dispatched : next state with
  | none => simp [respond, dispatched]
  | some command =>
    have notSign : command.kind ≠ .sign := by
      intro same
      cases command <;> simp_all [Command.kind]
      have guarded := next_sign_requires_review_and_revalidation reviewed state dispatched
      have prior := acknowledged_implies_called reviewed state .sign signed
      simp [prior] at guarded
    simpa [respond, dispatched] using
      non_sign_decision_preserves_payload reviewed state command reply notSign

end Tornado.Spec.WithdrawalDriver

#print axioms Tornado.Spec.WithdrawalDriver.prepared_review_is_actual_builder
#print axioms Tornado.Spec.WithdrawalDriver.finalized_changes_only_signature
#print axioms Tornado.Spec.WithdrawalDriver.finalized_binds_full_authorized_bytes
#print axioms Tornado.Spec.WithdrawalDriver.response_records_dispatched_command
#print axioms Tornado.Spec.WithdrawalDriver.next_sign_requires_review_and_revalidation
#print axioms Tornado.Spec.WithdrawalDriver.next_exposure_mark_requires_reservation
#print axioms Tornado.Spec.WithdrawalDriver.next_simulation_requires_prior_acks
#print axioms Tornado.Spec.WithdrawalDriver.next_send_requires_prior_acks
#print axioms Tornado.Spec.WithdrawalDriver.exposure_ack_fields
#print axioms Tornado.Spec.WithdrawalDriver.failed_reservation_blocks_exposure
#print axioms Tornado.Spec.WithdrawalDriver.failed_exposure_mark_blocks_network
#print axioms Tornado.Spec.WithdrawalDriver.lost_send_reply_keeps_unknown_path
#print axioms Tornado.Spec.WithdrawalDriver.rejected_simulation_keeps_unknown_path
#print axioms Tornado.Spec.WithdrawalDriver.unknown_phase_is_terminal
#print axioms Tornado.Spec.WithdrawalDriver.prior_exposure_blocks_new_signature
#print axioms Tornado.Spec.WithdrawalDriver.prior_send_blocks_second_send
#print axioms Tornado.Spec.WithdrawalDriver.acknowledged_event_is_in_prior_trace
#print axioms Tornado.Spec.WithdrawalDriver.dispatched_network_has_prior_successes
#print axioms Tornado.Spec.WithdrawalDriver.reachable_callback_count_at_most_one
#print axioms Tornado.Spec.WithdrawalDriver.reachable_one_signature_and_submission
#print axioms Tornado.Spec.WithdrawalDriver.returned_report_has_global_callback_cap
#print axioms Tornado.Spec.WithdrawalDriver.signed_payload_is_stable
#print axioms Tornado.Spec.WithdrawalDriver.kind_beq_eq
#print axioms Tornado.Spec.WithdrawalDriver.absent_call_count_zero
#print axioms Tornado.Spec.WithdrawalDriver.unique_dispatched_command_has_no_prior_call
#print axioms Tornado.Spec.WithdrawalDriver.acknowledged_implies_called
#print axioms Tornado.Spec.WithdrawalDriver.non_sign_decision_preserves_payload
