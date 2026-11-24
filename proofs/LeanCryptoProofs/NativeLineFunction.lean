import LeanCryptoProofs.CurveFunctionEvaluation
import LeanCryptoProofs.TateAffineConstruction
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing BN254Fp12

/-- The actual native addition step returns the partial evaluation of the
independent elliptic-curve rational line/vertical function. -/
theorem native_add_function (r s evaluation : Point) (evaluationCurve : evaluation.onCurve = true)
    (distinctX : model r.x ≠ model s.x)
    (vertical : model evaluation.x - model (sumFromSlope r s (addSlope r s)).x ≠ 0)
    (line : lineValue r evaluation (addSlope r s) ≠ 0) :
    ∃ factor : Fp12,
      nativeLineAndSum r s evaluation = .ok (factor, some (sumFromSlope r s (addSlope r s))) ∧
      Evaluates evaluation evaluationCurve
        (lineQuotient (model r.x) (model r.y) (addSlope r s)
          (model (sumFromSlope r s (addSlope r s)).x)) (model factor) := by
  refine ⟨_, line_add_construct r s evaluation distinctX vertical line, ?_⟩
  simp only [model_encode]
  exact lineQuotient_evaluates evaluation evaluationCurve _ _ _ _ vertical

theorem native_double_function (point evaluation : Point) (evaluationCurve : evaluation.onCurve = true)
    (nonzeroY : model point.y ≠ 0)
    (vertical : model evaluation.x - model (sumFromSlope point point (doubleSlope point)).x ≠ 0)
    (line : lineValue point evaluation (doubleSlope point) ≠ 0) :
    ∃ factor : Fp12,
      nativeLineAndSum point point evaluation = .ok (factor, some (sumFromSlope point point (doubleSlope point))) ∧
      Evaluates evaluation evaluationCurve
        (lineQuotient (model point.x) (model point.y) (doubleSlope point)
          (model (sumFromSlope point point (doubleSlope point)).x)) (model factor) := by
  refine ⟨_, line_double_construct point evaluation nonzeroY vertical line, ?_⟩
  simp only [model_encode]
  exact lineQuotient_evaluates evaluation evaluationCurve _ _ _ _ vertical

theorem verticalFunction_evaluates (point : Point) (onCurve : point.onCurve = true) (x : Field) :
    Evaluates point onCurve (verticalFunction x) (model point.x - x) := by
  refine ⟨verticalClass x, 1, ?_, ?_, ?_⟩
  · simp [verticalFunction]
  · simp
  · simp [evaluate_vertical]

theorem native_vertical_function (r s evaluation : Point) (evaluationCurve : evaluation.onCurve = true)
    (sameX : model r.x = model s.x) (negativeY : model r.y = -model s.y)
    (vertical : model evaluation.x - model r.x ≠ 0) :
    nativeLineAndSum r s evaluation = .ok (evaluation.x.sub r.x, none) ∧
      Evaluates evaluation evaluationCurve (verticalFunction (model r.x)) (model (evaluation.x.sub r.x)) := by
  refine ⟨line_vertical_construct r s evaluation sameX negativeY vertical, ?_⟩
  rw [model_sub]
  exact verticalFunction_evaluates evaluation evaluationCurve _

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.native_add_function
#print axioms LeanCrypto.Proofs.BN254Tate.native_double_function
#print axioms LeanCrypto.Proofs.BN254Tate.verticalFunction_evaluates
#print axioms LeanCrypto.Proofs.BN254Tate.native_vertical_function
