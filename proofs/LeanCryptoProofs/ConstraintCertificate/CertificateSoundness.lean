import LeanCryptoProofs.ConstraintCertificate.CertificateTargets
set_option autoImplicit false

namespace LeanCrypto.Proofs.ConstraintCertificate

open LeanCrypto.Groth16.ConstraintCertificate

/-- The actual public checker transfers all original source equations to
all actual targets. The assignment is mathematical input to the theorem;
the runtime checker and certificate never contain a secret assignment. -/
theorem checkCertificate_sound (nVars nSignals : Nat) (linears : Array Linear)
    (nonlinear targets : Array Equation) (certificate : Certificate)
    (assignment : Nat → Fr) (constant : assignment 0 = 1)
    (linearSources : RowsZero assignment linears)
    (nonlinearSources : EquationsSatisfied assignment nonlinear)
    (returned : checkCertificate nVars nSignals linears nonlinear targets certificate = .ok ()) :
    EquationsSatisfied assignment targets ∧ targets.all (equationAdmitted nVars) = true := by
  by_cases dimensions : dimensionsInvalid nVars nSignals linears nonlinear targets certificate = true
  · simp only [checkCertificate, dimensions, ↓reduceIte] at returned
    change (Except.error "Constraint-certificate dimensions are invalid." : Except String Unit) = .ok () at returned
    contradiction
  · by_cases admitted : rowsInvalid nVars nSignals linears nonlinear targets = true
    · simp only [checkCertificate, dimensions, admitted, ↓reduceIte] at returned
      change (Except.error "Constraint-certificate source or target row is invalid." : Except String Unit) = .ok () at returned
      contradiction
    · have targetAdmitted : targets.all (equationAdmitted nVars) = true := by
        by_contra rejected
        have failed : targets.all (equationAdmitted nVars) = false := Bool.eq_false_iff.mpr rejected
        simp only [rowsInvalid, failed, Bool.not_false, Bool.or_true, not_true_eq_false] at admitted
      by_cases budget : substitutionCount certificate > maximumSubstitutionSteps
      · simp only [checkCertificate, dimensions, admitted, budget, ↓reduceIte] at returned
        change (Except.error "Constraint-certificate substitution budget exceeded." : Except String Unit) = .ok () at returned
        contradiction
      · simp only [checkCertificate, dimensions, admitted, budget, ↓reduceIte] at returned
        change (do
          let rows ← deriveRows linears certificate.steps
          checkRules nVars nSignals rows certificate.rules
          let substituted ← substituteAll nVars rows certificate.rules nonlinear certificate.substitutions
          checkMatches substituted targets certificate.matches) = .ok () at returned
        cases derived : deriveRows linears certificate.steps with
        | error failure =>
          rw [derived] at returned
          change (Except.error failure : Except String Unit) = .ok () at returned
          contradiction
        | ok rows =>
          rw [derived] at returned
          change (do
            checkRules nVars nSignals rows certificate.rules
            let substituted ← substituteAll nVars rows certificate.rules nonlinear certificate.substitutions
            checkMatches substituted targets certificate.matches) = .ok () at returned
          have zero := deriveRows_zero assignment linears certificate.steps linearSources rows derived
          cases rulesChecked : checkRules nVars nSignals rows certificate.rules with
          | error failure =>
            rw [rulesChecked] at returned
            change (Except.error failure : Except String Unit) = .ok () at returned
            contradiction
          | ok checkedUnit =>
            cases checkedUnit
            rw [rulesChecked] at returned
            change (do
              let substituted ← substituteAll nVars rows certificate.rules nonlinear certificate.substitutions
              checkMatches substituted targets certificate.matches) = .ok () at returned
            cases replaced : substituteAll nVars rows certificate.rules nonlinear certificate.substitutions with
            | error failure =>
              rw [replaced] at returned
              change (Except.error failure : Except String Unit) = .ok () at returned
              contradiction
            | ok substituted =>
              rw [replaced] at returned
              have satisfied := substituteAll_satisfies assignment nVars rows certificate.rules zero nonlinear
                certificate.substitutions nonlinearSources substituted replaced
              exact ⟨checkMatches_satisfies assignment constant substituted targets certificate.matches satisfied returned,
                targetAdmitted⟩

theorem evalSparse_congr {Key : Type} (left right : Key → Fr) (row : List (Key × Nat))
    (equal : ∀ term ∈ row, left term.1 = right term.1) : evalSparse left row = evalSparse right row := by
  induction row with
  | nil => rfl
  | cons term rest ih =>
    rw [evalSparse, evalSparse, equal term (by simp)]
    rw [ih (fun value member => equal value (by simp only [List.mem_cons]; exact Or.inr member))]

theorem linearValue_prefix (nVars : Nat) (left right : Nat → Fr)
    (agrees : ∀ index, index < nVars → left index = right index) (row : Linear)
    (admitted : rowAdmitted nVars row = true) : linearValue left row = linearValue right row := by
  apply evalSparse_congr
  intro term member
  simp only [rowAdmitted, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at admitted
  exact agrees term.1 ((admitted.2 term member).1)

theorem satisfies_prefix (nVars : Nat) (left right : Nat → Fr)
    (agrees : ∀ index, index < nVars → left index = right index) (equation : Equation)
    (admitted : equationAdmitted nVars equation = true)
    (satisfied : Satisfies left equation) : Satisfies right equation := by
  simp only [equationAdmitted, Bool.and_eq_true] at admitted
  unfold Satisfies at *
  rw [← linearValue_prefix nVars left right agrees equation.a admitted.1.1,
    ← linearValue_prefix nVars left right agrees equation.b admitted.1.2,
    ← linearValue_prefix nVars left right agrees equation.c admitted.2]
  exact satisfied

/-- Auxiliary graph slots are erased from the target conclusion: target
equations concern only the original nVars prefix, checked by the runtime. -/
theorem checkCertificate_prefix_sound (nVars nSignals : Nat) (linears : Array Linear)
    (nonlinear targets : Array Equation) (certificate : Certificate)
    (extended original : Nat → Fr) (constant : extended 0 = 1)
    (agrees : ∀ index, index < nVars → extended index = original index)
    (linearSources : RowsZero extended linears)
    (nonlinearSources : EquationsSatisfied extended nonlinear)
    (returned : checkCertificate nVars nSignals linears nonlinear targets certificate = .ok ()) :
    EquationsSatisfied original targets := by
  obtain ⟨satisfied, admitted⟩ := checkCertificate_sound nVars nSignals linears nonlinear targets certificate
    extended constant linearSources nonlinearSources returned
  intro target member
  apply satisfies_prefix nVars extended original agrees target _ (satisfied target member)
  obtain ⟨index, bounded, equal⟩ := Array.mem_iff_getElem.mp member
  have all := Array.all_eq_true.mp admitted index bounded
  simpa only [equal] using all

end LeanCrypto.Proofs.ConstraintCertificate

#print axioms LeanCrypto.Proofs.ConstraintCertificate.checkCertificate_sound
#print axioms LeanCrypto.Proofs.ConstraintCertificate.evalSparse_congr
#print axioms LeanCrypto.Proofs.ConstraintCertificate.linearValue_prefix
#print axioms LeanCrypto.Proofs.ConstraintCertificate.satisfies_prefix
#print axioms LeanCrypto.Proofs.ConstraintCertificate.checkCertificate_prefix_sound
