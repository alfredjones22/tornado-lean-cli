import Tornado.Policy

namespace Tornado.Policy

/-- A successful native simulation gate has the exact normalized operation hash. -/
theorem simulation_hash_matches (result : Simulation) (quote : BatchQuote) (now : Int)
    (h : canSubmitSimulation result quote now = true) :
    result.userOpHash.toLower = quote.userOpHash.toLower := by
  simp only [canSubmitSimulation, Bool.and_eq_true] at h
  exact (beq_iff_eq).mp h.1.1

/-- Successful admission satisfies the same upper age bound as the executable gate. -/
theorem simulation_within_upper_age_bound (result : Simulation) (quote : BatchQuote) (now : Int)
    (h : canSubmitSimulation result quote now = true) :
    now - result.checkedAt < 300000 := by
  simp only [canSubmitSimulation, Bool.and_eq_true] at h
  exact decide_eq_true_eq.mp h.1.2

/-- The native gate cannot admit an explicit failed simulation. -/
theorem failed_simulation_blocks (result : Simulation) (quote : BatchQuote) (now : Int)
    (h : result.status = .failed) :
    canSubmitSimulation result quote now = false := by
  simp [canSubmitSimulation, h]

/-- The native fee validator returns exactly its checked arithmetic result. -/
theorem relayer_fee_fields (input : RelayerFeeInput) (result : RelayerFeeResult)
    (h : validateRelayerFee input = some result) :
    result.fee = input.fee ∧ result.net = input.amount - input.fee ∧
      result.serviceFee = input.amount * input.serviceFeeBps / 10000 ∧
      result.networkFee = input.fee - result.serviceFee := by
  unfold validateRelayerFee at h
  split at h
  · dsimp at h
    split at h
    · contradiction
    · cases h
      simp
  · contradiction

/-- A returned fee quote has passed every native amount and cap guard. -/
theorem relayer_fee_limits (input : RelayerFeeInput) (result : RelayerFeeResult)
    (h : validateRelayerFee input = some result) : relayerFeeWithinLimits input := by
  unfold validateRelayerFee at h
  split at h
  · assumption
  · contradiction

/-- The returned net plus relayer fee equals the selected note amount. -/
theorem relayer_fee_conserves_amount (input : RelayerFeeInput) (result : RelayerFeeResult)
    (h : validateRelayerFee input = some result) : result.net + result.fee = input.amount := by
  have fields := relayer_fee_fields input result h
  have limits := relayer_fee_limits input result h
  rcases fields with ⟨hfee, hnet, _, _⟩
  rcases limits with ⟨_, _, _, hlt, _⟩
  rw [hfee, hnet]
  exact Nat.sub_add_cancel (Nat.le_of_lt hlt)

/-- Unknown outcomes cannot start a fresh attempt in the native policy. -/
theorem unknown_blocks_retry (state : Attempt) (h : state.phase = .unknown) :
    retryAllowed state = false := by
  simp [retryAllowed, h]

/-- There is no second send transition from an already submitted attempt. -/
theorem submitted_cannot_send_again (state : Attempt) (h : state.phase = .submitted) :
    stepAttempt state .send = .error "Submission requires a matching reservation and no earlier send." := by
  simp [stepAttempt, h]

/-- A direct send transition must have been entered from the exposed phase. -/
theorem send_requires_exposed (before after : Attempt)
    (h : stepAttempt before .send = .ok after) : before.phase = .exposed := by
  cases hp : before.phase <;> simp [stepAttempt, hp] at h ⊢

/-- Successful send is possible only for the same reserved signature, once. -/
theorem send_requires_matching_reservation (before after : Attempt)
    (h : stepAttempt before .send = .ok after) :
    before.reservedHash = before.signedHash ∧ before.reservedHash.isSome = true ∧
      before.sends = 0 ∧ after.sends = 1 := by
  cases hp : before.phase <;> simp [stepAttempt, hp] at h
  case exposed =>
    split at h
    · rename_i guard
      have hmatch := guard.1.1
      have hsome := guard.1.2
      have hzero := guard.2
      cases h
      exact ⟨hmatch, hsome, hzero, rfl⟩
    · contradiction

/-- Signing in the executable policy binds the signature hash to approval. -/
theorem sign_requires_review_match (before after : Attempt) (hash : String)
    (h : stepAttempt before (.sign hash) = .ok after) :
    before.reviewedHash = some hash ∧ after.signedHash = some hash := by
  dsimp [stepAttempt] at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    have hmatch := guard.2
    cases h
    exact ⟨hmatch, rfl⟩
  · contradiction

/-- The native reservation copies the already reviewed, signed hash. -/
theorem reservation_binds_reviewed_signature (before after : Attempt)
    (h : stepAttempt before .reserve = .ok after) :
    before.reviewedHash = before.signedHash ∧
      after.reservedHash = before.signedHash := by
  dsimp [stepAttempt] at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    have hmatch := guard.1.2
    cases h
    exact ⟨hmatch, rfl⟩
  · contradiction

/-- Exposure can occur only from a matching reserved signature. -/
theorem exposure_requires_matching_reservation (before after : Attempt)
    (h : stepAttempt before .expose = .ok after) :
    before.reservedHash = before.signedHash ∧ before.reservedHash.isSome = true := by
  dsimp [stepAttempt] at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    exact ⟨guard.1.2, guard.2⟩
  · contradiction

/-- Direct confirmation cannot be recorded without all three chain checks. -/
theorem confirmation_requires_exact_evidence (before after : Attempt)
    (evidence : ConfirmationEvidence)
    (h : stepAttempt before (.confirm evidence) = .ok after) :
    evidence.receiptSuccess = true ∧ evidence.entryPointEventMatches = true ∧
      evidence.withdrawalEventMatches = true := by
  dsimp [stepAttempt] at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true] at guard
    exact ⟨guard.1.1.2, guard.1.2, guard.2⟩
  · contradiction

end Tornado.Policy

#print axioms Tornado.Policy.simulation_hash_matches
#print axioms Tornado.Policy.simulation_within_upper_age_bound
#print axioms Tornado.Policy.failed_simulation_blocks
#print axioms Tornado.Policy.relayer_fee_fields
#print axioms Tornado.Policy.relayer_fee_limits
#print axioms Tornado.Policy.relayer_fee_conserves_amount
#print axioms Tornado.Policy.unknown_blocks_retry
#print axioms Tornado.Policy.submitted_cannot_send_again
#print axioms Tornado.Policy.send_requires_exposed
#print axioms Tornado.Policy.send_requires_matching_reservation
#print axioms Tornado.Policy.sign_requires_review_match
#print axioms Tornado.Policy.reservation_binds_reviewed_signature
#print axioms Tornado.Policy.exposure_requires_matching_reservation
#print axioms Tornado.Policy.confirmation_requires_exact_evidence
