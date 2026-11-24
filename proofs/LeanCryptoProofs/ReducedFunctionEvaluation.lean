import LeanCryptoProofs.LineFunctionStar
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

theorem evaluateCoordinate_constant (point : Point) (onCurve : point.onCurve = true)
    (value : BN254Fp12.Field) :
    evaluateCoordinate point onCurve (algebraMap BN254Fp12.Field CoordinateRing value) = value := by
  change (AdjoinRoot.lift (Polynomial.evalRingHom (BN254Fp12.model point.x))
    (BN254Fp12.model point.y) _) (AdjoinRoot.of curve12.toAffine.polynomial (Polynomial.C value)) = value
  rw [AdjoinRoot.lift_of]
  simp

theorem evaluates_constantFunction (point : Point) (onCurve : point.onCurve = true)
    (value : BN254Fp12.Field) : Evaluates point onCurve (constantFunction value) value := by
  refine ⟨algebraMap BN254Fp12.Field CoordinateRing value, 1, ?_, ?_, ?_⟩
  · simp [constantFunction]
  · simp
  · rw [evaluateCoordinate_constant, map_one, div_one]

theorem constant_ratio_star_fixed (first second scale : FunctionField)
    (firstNonzero : first ≠ 0) (scaleNonzero : scale ≠ 0)
    (constant : BN254Fp12.Field) (relation : second = constantFunction constant * first)
    (firstStar : functionStar first = scale * first) (secondStar : functionStar second = scale * second) :
    star constant = constant := by
  have transformed := congrArg functionStar relation
  rw [map_mul, functionStar_constantFunction, firstStar, secondStar, relation] at transformed
  have constants : constantFunction constant = constantFunction (star constant) := by
    apply mul_right_cancel₀ (mul_ne_zero scaleNonzero firstNonzero)
    calc
      constantFunction constant * (scale * first) = scale * (constantFunction constant * first) := by ring
      _ = _ := transformed
  exact (constantFunction_injective constants).symm

/-- Equal principal ideals and a common coefficient-star character force
identical reduced evaluations. The ratio constant is proved to lie in Fp6,
whose multiplicative order divides the pinned final exponent. -/
theorem principal_common_star_reduced (point : Point) (onCurve : point.onCurve = true)
    (first second scale : FunctionField) (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0)
    (scaleNonzero : scale ≠ 0)
    (same : principal first firstNonzero = principal second secondNonzero)
    (firstStar : functionStar first = scale * first) (secondStar : functionStar second = scale * second)
    (firstValue secondValue : BN254Fp12.Field)
    (firstEvaluated : Evaluates point onCurve first firstValue)
    (secondEvaluated : Evaluates point onCurve second secondValue) :
    secondValue ^ finalExponent = firstValue ^ finalExponent := by
  obtain ⟨constant, nonzero, relation⟩ := principal_equal_constant first second firstNonzero secondNonzero same
  have fixed := constant_ratio_star_fixed first second scale firstNonzero scaleNonzero constant relation firstStar secondStar
  have killed := star_fixed_reduces_one constant nonzero fixed
  have evaluated := evaluates_mul point onCurve (constantFunction constant) first constant firstValue
    (evaluates_constantFunction point onCurve constant) firstEvaluated
  rw [← relation] at evaluated
  have values := evaluates_unique point onCurve second secondValue (constant * firstValue) secondEvaluated evaluated
  rw [values, mul_pow, killed, one_mul]

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.evaluateCoordinate_constant
#print axioms LeanCrypto.Proofs.BN254Tate.evaluates_constantFunction
#print axioms LeanCrypto.Proofs.BN254Tate.constant_ratio_star_fixed
#print axioms LeanCrypto.Proofs.BN254Tate.principal_common_star_reduced
