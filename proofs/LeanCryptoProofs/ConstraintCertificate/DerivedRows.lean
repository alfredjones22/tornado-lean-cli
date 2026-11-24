import LeanCryptoProofs.ConstraintCertificate.CheckedLoops
set_option autoImplicit false

namespace LeanCrypto.Proofs.ConstraintCertificate

open LeanCrypto.Groth16.ConstraintCertificate

def RowsZero (assignment : Nat → Fr) (rows : Array Linear) : Prop :=
  ∀ row ∈ rows, linearValue assignment row = 0

theorem rowsZero_get (assignment : Nat → Fr) (rows : Array Linear) (zero : RowsZero assignment rows)
    (index : Nat) (bounded : index < rows.size) : linearValue assignment rows[index]! = 0 := by
  apply zero
  simpa only [getElem!_pos rows index bounded] using Array.getElem_mem bounded

theorem rowsZero_push (assignment : Nat → Fr) (rows : Array Linear) (row : Linear)
    (zero : RowsZero assignment rows) (nextZero : linearValue assignment row = 0) :
    RowsZero assignment (rows.push row) := by
  intro value member
  rw [Array.mem_push] at member
  rcases member with old | equal
  · exact zero value old
  · simpa only [equal] using nextZero

theorem rowsZero_normalize (assignment : Nat → Fr) (rows : Array Linear) (zero : RowsZero assignment rows) :
    RowsZero assignment (rows.map normalizeLinear) := by
  intro row member
  obtain ⟨original, originalMember, equal⟩ := Array.mem_map.mp member
  rw [← equal, linear_normalize]
  exact zero original originalMember

theorem deriveStep_zero (assignment : Nat → Fr) (rows : Array Linear) (step : LinearStep)
    (zero : RowsZero assignment rows) (output : Linear) (returned : deriveStep rows step = .ok output) :
    linearValue assignment output = 0 := by
  cases step with
  | scale source scalar =>
    simp only [deriveStep] at returned
    split at returned
    · change (Except.error "Invalid constraint-certificate scale reference." : Except String Linear) = .ok output at returned
      contradiction
    · rename_i admitted
      have bounded : source < rows.size := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at admitted
        omega
      have equal : scaleLinear scalar rows[source]! = output := Except.ok.inj returned
      rw [← equal, linear_scale, rowsZero_get assignment rows zero source bounded, mul_zero]
  | add left right =>
    simp only [deriveStep] at returned
    split at returned
    · change (Except.error "Invalid constraint-certificate addition reference." : Except String Linear) = .ok output at returned
      contradiction
    · rename_i admitted
      have bounded : left < rows.size ∧ right < rows.size := by
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at admitted
        omega
      have equal : addLinear rows[left]! rows[right]! = output := Except.ok.inj returned
      rw [← equal, linear_add, rowsZero_get assignment rows zero left bounded.1,
        rowsZero_get assignment rows zero right bounded.2, add_zero]

def deriveEffect (step : LinearStep) (rows : Array Linear) : Except String (ForInStep (Array Linear)) := do
  let next ← deriveStep rows step
  if next.length > maximumWorkingWidth then
    throw "Constraint-certificate working row is too wide."
  pure (ForInStep.yield (rows.push next))

theorem deriveEffect_preserves (assignment : Nat → Fr) (step : LinearStep) (rows : Array Linear)
    (zero : RowsZero assignment rows) (next : ForInStep (Array Linear))
    (returned : deriveEffect step rows = .ok next) : RowsZero assignment next.value := by
  unfold deriveEffect at returned
  cases result : deriveStep rows step with
  | error failure =>
    rw [result] at returned
    change (Except.error failure : Except String (ForInStep (Array Linear))) = .ok next at returned
    contradiction
  | ok row =>
    rw [result] at returned
    have nextZero := deriveStep_zero assignment rows step zero row result
    change (if row.length > maximumWorkingWidth then
      (throw "Constraint-certificate working row is too wide." : Except String PUnit) >>= fun _ => pure (ForInStep.yield (rows.push row))
      else (pure PUnit.unit : Except String PUnit) >>= fun _ => pure (ForInStep.yield (rows.push row))) = .ok next at returned
    split at returned
    · change (Except.error "Constraint-certificate working row is too wide." : Except String (ForInStep (Array Linear))) = .ok next at returned
      contradiction
    · have equal : ForInStep.yield (rows.push row) = next := Except.ok.inj returned
      rw [← equal]
      exact rowsZero_push assignment rows row zero nextZero

theorem deriveRows_source (initial : Array Linear) (steps : Array LinearStep) :
    deriveRows initial steps =
      ForIn.forIn steps.toList (initial.map normalizeLinear) deriveEffect := by
  change (do
    let result ← ForIn.forIn steps (initial.map normalizeLinear) deriveEffect
    pure result) = ForIn.forIn steps.toList (initial.map normalizeLinear) deriveEffect
  simp only [bind_pure, Array.forIn_toList]

theorem deriveRows_zero (assignment : Nat → Fr) (initial : Array Linear) (steps : Array LinearStep)
    (zero : RowsZero assignment initial) (output : Array Linear)
    (returned : deriveRows initial steps = .ok output) : RowsZero assignment output := by
  rw [deriveRows_source] at returned
  exact forIn_success_invariant steps.toList deriveEffect (RowsZero assignment)
    (fun step _ rows old next effect => deriveEffect_preserves assignment step rows old next effect)
    (initial.map normalizeLinear) (rowsZero_normalize assignment initial zero) output returned

end LeanCrypto.Proofs.ConstraintCertificate

#print axioms LeanCrypto.Proofs.ConstraintCertificate.rowsZero_get
#print axioms LeanCrypto.Proofs.ConstraintCertificate.rowsZero_push
#print axioms LeanCrypto.Proofs.ConstraintCertificate.rowsZero_normalize
#print axioms LeanCrypto.Proofs.ConstraintCertificate.deriveStep_zero
#print axioms LeanCrypto.Proofs.ConstraintCertificate.deriveEffect_preserves
#print axioms LeanCrypto.Proofs.ConstraintCertificate.deriveRows_source
#print axioms LeanCrypto.Proofs.ConstraintCertificate.deriveRows_zero
