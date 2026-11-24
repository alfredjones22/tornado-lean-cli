import LeanCryptoProofs.ConstraintCertificate.Substitution
set_option autoImplicit false

namespace LeanCrypto.Proofs.ConstraintCertificate

open LeanCrypto.Groth16.ConstraintCertificate

def EquationsSatisfied (assignment : Nat → Fr) (equations : Array Equation) : Prop :=
  ∀ equation ∈ equations, Satisfies assignment equation

theorem satisfied_get (assignment : Nat → Fr) (equations : Array Equation)
    (satisfied : EquationsSatisfied assignment equations) (index : Nat) (bounded : index < equations.size) :
    Satisfies assignment equations[index]! := by
  apply satisfied
  simpa only [getElem!_pos equations index bounded] using Array.getElem_mem bounded

theorem satisfied_push (assignment : Nat → Fr) (equations : Array Equation) (next : Equation)
    (satisfied : EquationsSatisfied assignment equations) (nextSatisfied : Satisfies assignment next) :
    EquationsSatisfied assignment (equations.push next) := by
  intro equation member
  rw [Array.mem_push] at member
  rcases member with old | equal
  · exact satisfied equation old
  · simpa only [equal] using nextSatisfied

def substituteAllEffect (nVars : Nat) (rows : Array Linear) (rules : Array Rule)
    (nonlinear : Array Equation) (programs : Array Substitution)
    (index : Nat) (current : Array Equation) : Except String (ForInStep (Array Equation)) := do
  let next ← substituteEquation nVars rows rules nonlinear[index]! programs[index]!
  pure (ForInStep.yield (current.push next))

theorem substituteAllEffect_preserves (assignment : Nat → Fr) (nVars : Nat) (rows : Array Linear)
    (rules : Array Rule) (zero : RowsZero assignment rows) (nonlinear : Array Equation)
    (programs : Array Substitution) (sources : EquationsSatisfied assignment nonlinear)
    (index : Nat) (bounded : index < nonlinear.size) (current : Array Equation)
    (satisfied : EquationsSatisfied assignment current) (next : ForInStep (Array Equation))
    (returned : substituteAllEffect nVars rows rules nonlinear programs index current = .ok next) :
    EquationsSatisfied assignment next.value := by
  unfold substituteAllEffect at returned
  cases result : substituteEquation nVars rows rules nonlinear[index]! programs[index]! with
  | error failure =>
    rw [result] at returned
    change (Except.error failure : Except String (ForInStep (Array Equation))) = .ok next at returned
    contradiction
  | ok equation =>
    rw [result] at returned
    have equal : ForInStep.yield (current.push equation) = next := Except.ok.inj returned
    rw [← equal]
    apply satisfied_push assignment current equation satisfied
    exact substituteEquation_satisfies assignment rows rules zero nVars nonlinear[index]! programs[index]!
      (satisfied_get assignment nonlinear sources index bounded) equation result

theorem substituteAll_source (nVars : Nat) (rows : Array Linear) (rules : Array Rule)
    (nonlinear : Array Equation) (programs : Array Substitution) :
    substituteAll nVars rows rules nonlinear programs =
      ForIn.forIn (List.range nonlinear.size) #[] (substituteAllEffect nVars rows rules nonlinear programs) := by
  change (do
    let result ← ForIn.forIn [0:nonlinear.size] #[] (substituteAllEffect nVars rows rules nonlinear programs)
    pure result) = _
  simp [List.range_eq_range']

theorem substituteAll_satisfies (assignment : Nat → Fr) (nVars : Nat) (rows : Array Linear)
    (rules : Array Rule) (zero : RowsZero assignment rows) (nonlinear : Array Equation)
    (programs : Array Substitution) (sources : EquationsSatisfied assignment nonlinear)
    (output : Array Equation) (returned : substituteAll nVars rows rules nonlinear programs = .ok output) :
    EquationsSatisfied assignment output := by
  rw [substituteAll_source] at returned
  apply forIn_success_invariant (List.range nonlinear.size) (substituteAllEffect nVars rows rules nonlinear programs)
    (EquationsSatisfied assignment) _ #[] (by simp [EquationsSatisfied]) output returned
  intro index member current currentSatisfied next effect
  exact substituteAllEffect_preserves assignment nVars rows rules zero nonlinear programs sources index
    (List.mem_range.mp member) current currentSatisfied next effect

theorem checkMatch_satisfies (assignment : Nat → Fr) (constant : assignment 0 = 1)
    (substituted : Array Equation) (satisfied : EquationsSatisfied assignment substituted)
    (target : Equation) (selected : Match) (returned : checkMatch substituted target selected = .ok ()) :
    Satisfies assignment target := by
  by_cases references : (decide (selected.source >= substituted.size) || selected.scale == 0 || decide (selected.scale >= modulus)) = true
  · simp only [checkMatch, references, ↓reduceIte] at returned
    change (Except.error "Constraint-certificate target reference is invalid." : Except String Unit) = .ok () at returned
    contradiction
  · have bounded : selected.source < substituted.size := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or] at references
      omega
    by_cases width : target.a.length * target.b.length + target.c.length > maximumPolynomialTerms
    · simp only [checkMatch, references, width, ↓reduceIte] at returned
      change (Except.error "Constraint-certificate target polynomial is too large." : Except String Unit) = .ok () at returned
      contradiction
    · by_cases correspondence : (equationPolynomial target != scaleQuadratic selected.scale
          (equationPolynomial substituted[selected.source]!)) = true
      · simp only [checkMatch, references, width, correspondence, ↓reduceIte] at returned
        change (Except.error "Constraint-certificate polynomial correspondence failed." : Except String Unit) = .ok () at returned
        contradiction
      · have equal : equationPolynomial target =
            scaleQuadratic selected.scale (equationPolynomial substituted[selected.source]!) := by
          apply bne_eq_false_iff_eq.mp
          exact Bool.eq_false_iff.mpr correspondence
        apply (satisfies_iff_polynomial_zero assignment constant target).2
        rw [equal, quadratic_scale,
          (satisfies_iff_polynomial_zero assignment constant substituted[selected.source]!).1
            (satisfied_get assignment substituted satisfied selected.source bounded), mul_zero]

theorem checkMatch_reference_bounds (substituted : Array Equation) (target : Equation) (selected : Match)
    (returned : checkMatch substituted target selected = .ok ()) :
    selected.source < substituted.size ∧ 0 < selected.scale ∧ selected.scale < modulus := by
  by_cases references : (decide (selected.source >= substituted.size) || selected.scale == 0 || decide (selected.scale >= modulus)) = true
  · simp only [checkMatch, references, ↓reduceIte] at returned
    change (Except.error "Constraint-certificate target reference is invalid." : Except String Unit) = .ok () at returned
    contradiction
  · simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or] at references
    omega

theorem checkMatch_scale_nonzero (substituted : Array Equation) (target : Equation) (selected : Match)
    (returned : checkMatch substituted target selected = .ok ()) :
    LeanCrypto.Proofs.BN254Fr.model selected.scale ≠ 0 := by
  obtain ⟨_, positive, bounded⟩ := checkMatch_reference_bounds substituted target selected returned
  change selected.scale < LeanCrypto.Proofs.BN254Fr.Q at bounded
  intro zero
  have native := (LeanCrypto.Proofs.BN254Fr.model_zero_iff selected.scale).1 zero
  rw [Nat.mod_eq_of_lt bounded] at native
  omega

theorem checkMatches_source (substituted targets : Array Equation) (selections : Array Match) :
    checkMatches substituted targets selections =
      ForIn.forIn (List.range targets.size) ()
        (checkEffect (fun index => checkMatch substituted targets[index]! selections[index]!)) := by
  change ((ForIn.forIn [0:targets.size] ()
    (checkEffect (fun index => checkMatch substituted targets[index]! selections[index]!))) >>= fun _ => pure ()) = _
  have finish (action : Except String Unit) : (action >>= fun _ => pure ()) = action := by
    cases action with
    | error _ => rfl
    | ok value => cases value; rfl
  rw [finish]
  simp [List.range_eq_range']

theorem checkMatches_satisfies (assignment : Nat → Fr) (constant : assignment 0 = 1)
    (substituted targets : Array Equation) (selections : Array Match)
    (satisfied : EquationsSatisfied assignment substituted)
    (returned : checkMatches substituted targets selections = .ok ()) : EquationsSatisfied assignment targets := by
  rw [checkMatches_source] at returned
  have checks := forIn_checks_succeed (List.range targets.size)
    (fun index => checkMatch substituted targets[index]! selections[index]!) returned
  intro target member
  obtain ⟨index, bounded, equal⟩ := Array.mem_iff_getElem.mp member
  have targetEqual : targets[index]! = target := by simpa only [getElem!_pos targets index bounded] using equal
  rw [← targetEqual]
  exact checkMatch_satisfies assignment constant substituted satisfied targets[index]! selections[index]!
    (checks index (List.mem_range.mpr bounded))

end LeanCrypto.Proofs.ConstraintCertificate

#print axioms LeanCrypto.Proofs.ConstraintCertificate.satisfied_get
#print axioms LeanCrypto.Proofs.ConstraintCertificate.satisfied_push
#print axioms LeanCrypto.Proofs.ConstraintCertificate.substituteAllEffect_preserves
#print axioms LeanCrypto.Proofs.ConstraintCertificate.substituteAll_source
#print axioms LeanCrypto.Proofs.ConstraintCertificate.substituteAll_satisfies
#print axioms LeanCrypto.Proofs.ConstraintCertificate.checkMatch_satisfies
#print axioms LeanCrypto.Proofs.ConstraintCertificate.checkMatch_reference_bounds
#print axioms LeanCrypto.Proofs.ConstraintCertificate.checkMatch_scale_nonzero
#print axioms LeanCrypto.Proofs.ConstraintCertificate.checkMatches_source
#print axioms LeanCrypto.Proofs.ConstraintCertificate.checkMatches_satisfies
