import LeanCryptoProofs.Elliptic12
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

def evaluateCoordinate (point : Point) (onCurve : point.onCurve = true) :
    CoordinateRing →+* BN254Fp12.Field :=
  AdjoinRoot.lift (Polynomial.evalRingHom (BN254Fp12.model point.x)) (BN254Fp12.model point.y)
    (by
      rw [Polynomial.eval₂_evalRingHom]
      change curve12.toAffine.Equation (BN254Fp12.model point.x) (BN254Fp12.model point.y)
      rw [WeierstrassCurve.Affine.equation_iff, curve12_coefficients]
      simpa using (native_onCurve_iff point).1 onCurve)

def verticalClass (x : BN254Fp12.Field) : CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.XClass curve12.toAffine x

def lineClass (x y slope : BN254Fp12.Field) : CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.YClass curve12.toAffine
    (WeierstrassCurve.Affine.linePolynomial x y slope)

def verticalFunction (x : BN254Fp12.Field) : FunctionField :=
  algebraMap CoordinateRing FunctionField (verticalClass x)

def lineFunction (x y slope : BN254Fp12.Field) : FunctionField :=
  algebraMap CoordinateRing FunctionField (lineClass x y slope)

def lineQuotient (x y slope sumX : BN254Fp12.Field) : FunctionField :=
  lineFunction x y slope / verticalFunction sumX

theorem verticalFunction_nonzero (x : BN254Fp12.Field) : verticalFunction x ≠ 0 := by
  intro zero
  apply WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero (W' := curve12.toAffine) x
  exact (IsFractionRing.injective CoordinateRing FunctionField) (by simpa [verticalFunction] using zero)

theorem lineFunction_nonzero (x y slope : BN254Fp12.Field) : lineFunction x y slope ≠ 0 := by
  intro zero
  apply WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero (W' := curve12.toAffine) _
  exact (IsFractionRing.injective CoordinateRing FunctionField) (by simpa [lineFunction] using zero)

theorem evaluate_vertical (point : Point) (onCurve : point.onCurve = true) (x : BN254Fp12.Field) :
    evaluateCoordinate point onCurve (verticalClass x) = BN254Fp12.model point.x - x := by
  simp [evaluateCoordinate, verticalClass, WeierstrassCurve.Affine.CoordinateRing.XClass,
    WeierstrassCurve.Affine.CoordinateRing.mk]

theorem evaluate_line (point : Point) (onCurve : point.onCurve = true) (x y slope : BN254Fp12.Field) :
    evaluateCoordinate point onCurve (lineClass x y slope) =
      (BN254Fp12.model point.y - y) - slope * (BN254Fp12.model point.x - x) := by
  simp [evaluateCoordinate, lineClass, WeierstrassCurve.Affine.CoordinateRing.YClass,
    WeierstrassCurve.Affine.CoordinateRing.mk, WeierstrassCurve.Affine.linePolynomial]
  ring

/-- Evaluation of a rational function at a point is partial: the selected
denominator must evaluate nonzero. No total field-to-field evaluation map
is assumed. -/
def Evaluates (point : Point) (onCurve : point.onCurve = true)
    (function : FunctionField) (value : BN254Fp12.Field) : Prop :=
  ∃ numerator denominator : CoordinateRing,
    function = algebraMap CoordinateRing FunctionField numerator /
      algebraMap CoordinateRing FunctionField denominator ∧
    evaluateCoordinate point onCurve denominator ≠ 0 ∧
    value = evaluateCoordinate point onCurve numerator / evaluateCoordinate point onCurve denominator

theorem lineQuotient_evaluates (point : Point) (onCurve : point.onCurve = true)
    (x y slope sumX : BN254Fp12.Field) (denominator : BN254Fp12.model point.x - sumX ≠ 0) :
    Evaluates point onCurve (lineQuotient x y slope sumX)
      (((BN254Fp12.model point.y - y) - slope * (BN254Fp12.model point.x - x)) /
        (BN254Fp12.model point.x - sumX)) := by
  refine ⟨lineClass x y slope, verticalClass sumX, rfl, ?_, ?_⟩
  · simpa only [evaluate_vertical] using denominator
  · rw [evaluate_line, evaluate_vertical]

theorem evaluates_unique (point : Point) (onCurve : point.onCurve = true)
    (function : FunctionField) (left right : BN254Fp12.Field)
    (first : Evaluates point onCurve function left) (second : Evaluates point onCurve function right) :
    left = right := by
  obtain ⟨n1, d1, f1, nz1, v1⟩ := first
  obtain ⟨n2, d2, f2, nz2, v2⟩ := second
  have d1Nonzero : d1 ≠ 0 := fun zero => nz1 (by rw [zero, map_zero])
  have d2Nonzero : d2 ≠ 0 := fun zero => nz2 (by rw [zero, map_zero])
  have injective := IsFractionRing.injective CoordinateRing FunctionField
  have image1 : algebraMap CoordinateRing FunctionField d1 ≠ 0 :=
    fun zero => d1Nonzero (injective (by simpa only [map_zero] using zero))
  have image2 : algebraMap CoordinateRing FunctionField d2 ≠ 0 :=
    fun zero => d2Nonzero (injective (by simpa only [map_zero] using zero))
  have cross := (div_eq_div_iff image1 image2).1 (f1.symm.trans f2)
  have baseCross : n1 * d2 = n2 * d1 := injective (by simpa only [map_mul] using cross)
  have evaluated := congrArg (evaluateCoordinate point onCurve) baseCross
  simp only [map_mul] at evaluated
  rw [v1, v2]
  exact (div_eq_div_iff nz1 nz2).2 evaluated

theorem evaluates_one (point : Point) (onCurve : point.onCurve = true) :
    Evaluates point onCurve 1 1 := by
  refine ⟨1, 1, ?_, ?_, ?_⟩ <;> simp

theorem evaluates_mul (point : Point) (onCurve : point.onCurve = true)
    (f g : FunctionField) (a b : BN254Fp12.Field)
    (first : Evaluates point onCurve f a) (second : Evaluates point onCurve g b) :
    Evaluates point onCurve (f * g) (a * b) := by
  obtain ⟨n1, d1, f1, nz1, v1⟩ := first
  obtain ⟨n2, d2, f2, nz2, v2⟩ := second
  refine ⟨n1 * n2, d1 * d2, ?_, ?_, ?_⟩
  · rw [f1, f2, map_mul, map_mul, div_mul_div_comm]
  · rw [map_mul]
    exact mul_ne_zero nz1 nz2
  · rw [v1, v2, map_mul, map_mul, div_mul_div_comm]

theorem evaluates_pow (point : Point) (onCurve : point.onCurve = true)
    (function : FunctionField) (value : BN254Fp12.Field)
    (evaluated : Evaluates point onCurve function value) (exponent : Nat) :
    Evaluates point onCurve (function ^ exponent) (value ^ exponent) := by
  induction exponent with
  | zero => simpa only [pow_zero] using evaluates_one point onCurve
  | succ n ih => simpa only [pow_succ] using evaluates_mul point onCurve _ _ _ _ ih evaluated

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.verticalFunction_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.lineFunction_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.evaluate_vertical
#print axioms LeanCrypto.Proofs.BN254Tate.evaluate_line
#print axioms LeanCrypto.Proofs.BN254Tate.lineQuotient_evaluates
#print axioms LeanCrypto.Proofs.BN254Tate.evaluates_unique
#print axioms LeanCrypto.Proofs.BN254Tate.evaluates_one
#print axioms LeanCrypto.Proofs.BN254Tate.evaluates_mul
#print axioms LeanCrypto.Proofs.BN254Tate.evaluates_pow
