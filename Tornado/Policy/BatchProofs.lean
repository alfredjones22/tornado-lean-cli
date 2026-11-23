import Tornado.Policy.Batch

namespace Tornado.Policy.Batch

/-- A prepared batch passed the native uniqueness, nonempty, and size gate. -/
theorem prepare_requires_valid_selection (before after : Attempt)
    (notes : List String) (hash : String)
    (h : step before (.prepare notes hash) = .ok after) :
    validSelection notes = true := by
  cases hv : validSelection notes with
  | false => simp [step, hv] at h
  | true => simp

/-- A successful signature transition copies the reviewed payload hash. -/
theorem sign_binds_reviewed_hash (before after : Attempt) (hash : String)
    (h : step before (.sign hash) = .ok after) :
    before.reviewedHash = some hash ∧ after.signedHash = some hash := by
  dsimp [step] at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    cases h
    exact ⟨guard.2, rfl⟩
  · contradiction

/-- A reservation can only name a selected, previously unreserved note. -/
theorem reserve_requires_selected_new_note (before after : Attempt) (note : String)
    (h : step before (.reserveNote note) = .ok after) :
    before.selected.contains note = true ∧ before.reserved.contains note = false := by
  dsimp [step] at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    simpa [List.contains_iff_mem] using And.intro guard.1.1.1.2 guard.1.1.2
  · contradiction

/-- Exposure is admitted only after every selected note has a reservation. -/
theorem exposure_requires_all_reserved (before after : Attempt)
    (h : step before .expose = .ok after) :
    allReserved before = true := by
  cases hr : allReserved before with
  | false => simp [step, hr] at h
  | true => simp

/-- A send also checks every selected note's reservation, even for forged state. -/
theorem send_requires_all_reserved (before after : Attempt)
    (h : step before .send = .ok after) :
    allReserved before = true := by
  cases hr : allReserved before with
  | false => simp [step, hr] at h
  | true => simp

/-- The native batch gate only sends from exposure, once. -/
theorem send_requires_first_exposure (before after : Attempt)
    (h : step before .send = .ok after) :
    before.phase = .exposed ∧ before.sends = 0 ∧ after.sends = 1 := by
  dsimp [step] at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    have hphase : before.phase = .exposed := by
      cases hp : before.phase
      all_goals first
        | rfl
        | have hb : (before.phase == Phase.exposed) = false := by rw [hp]; decide
          have hc := guard.1.1.1.1
          simp [hb] at hc
    have hzero : before.sends = 0 := guard.2
    cases h
    exact ⟨hphase, hzero, rfl⟩
  · contradiction

/-- Exposure cannot be followed by replacement signing. -/
theorem exposed_cannot_resign (state : Attempt) (hash : String)
    (h : state.phase = .exposed) :
    step state (.sign hash) = .error "The batch signature differs from the reviewed payload." := by
  have hb : (Phase.exposed == Phase.reviewed) = false := by decide
  simp [step, h, hb]

/-- Uncertain outcomes cannot be retried as a fresh operation. -/
theorem unknown_blocks_retry (state : Attempt) (h : state.phase = .unknown) :
    retryAllowed state = false := by
  have hb : (Phase.unknown == Phase.fresh) = false := by decide
  simp [retryAllowed, h, hb]

/-- The native gate requires a successful receipt and matching EntryPoint event. -/
theorem confirmation_requires_chain_success (before after : Attempt) (evidence : Evidence)
    (h : step before (.confirm evidence) = .ok after) :
    evidence.receiptSuccess = true ∧ evidence.entryPointEventMatches = true := by
  cases hr : evidence.receiptSuccess with
  | false => simp [step, hr] at h
  | true =>
    cases he : evidence.entryPointEventMatches with
    | false => simp [step, hr, he] at h
    | true => simp

/-- Confirmation requires exact selected-note event coverage. -/
theorem confirmation_requires_exact_note_events (before after : Attempt) (evidence : Evidence)
    (h : step before (.confirm evidence) = .ok after) :
    exactEvents before.selected evidence.matchedNullifiers = true := by
  cases he : exactEvents before.selected evidence.matchedNullifiers with
  | false => simp [step, he] at h
  | true => simp

end Tornado.Policy.Batch

#print axioms Tornado.Policy.Batch.prepare_requires_valid_selection
#print axioms Tornado.Policy.Batch.sign_binds_reviewed_hash
#print axioms Tornado.Policy.Batch.reserve_requires_selected_new_note
#print axioms Tornado.Policy.Batch.exposure_requires_all_reserved
#print axioms Tornado.Policy.Batch.send_requires_all_reserved
#print axioms Tornado.Policy.Batch.send_requires_first_exposure
#print axioms Tornado.Policy.Batch.exposed_cannot_resign
#print axioms Tornado.Policy.Batch.unknown_blocks_retry
#print axioms Tornado.Policy.Batch.confirmation_requires_chain_success
#print axioms Tornado.Policy.Batch.confirmation_requires_exact_note_events
