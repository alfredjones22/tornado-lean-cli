import LeanCryptoProofs.TwistEvaluation
import LeanCryptoProofs.TateAffineConstruction
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing BN254Fp12

theorem native12_equation (point : Point) (onCurve : point.onCurve = true) :
    curve12.toAffine.Equation (model point.x) (model point.y) := by
  rw [WeierstrassCurve.Affine.equation_iff, curve12_coefficients]
  simpa using (native_onCurve_iff point).1 onCurve

theorem nativeSum_x (r s : Point) (slope : Field) :
    model (sumFromSlope r s slope).x = curve12.toAffine.addX (model r.x) (model s.x) slope := by
  rw [sumFromSlope_x, curve12_addX]

theorem nativeSum_y (r s : Point) (slope : Field) :
    model (sumFromSlope r s slope).y = curve12.toAffine.addY (model r.x) (model s.x) (model r.y) slope := by
  rw [sumFromSlope_y, curve12_addY]

theorem nativeSum_onCurve (r s : Point) (rCurve : r.onCurve = true) (sCurve : s.onCurve = true)
    (notVertical : ¬(model r.x = model s.x ∧ model r.y = curve12.toAffine.negY (model s.x) (model s.y))) :
    (sumFromSlope r s (curve12.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y))).onCurve = true := by
  apply (native_onCurve_iff _).2
  have equation := WeierstrassCurve.Affine.equation_add (native12_equation r rCurve)
    (native12_equation s sCurve) notVertical
  have converted := (WeierstrassCurve.Affine.equation_iff _ _).1 equation
  rw [← nativeSum_x, ← nativeSum_y] at converted
  simpa only [curve12_coefficients, zero_mul, zero_add, add_zero] using converted

theorem nativeSum_modelPoint (r s : Point) (rCurve : r.onCurve = true) (sCurve : s.onCurve = true)
    (notVertical : ¬(model r.x = model s.x ∧ model r.y = curve12.toAffine.negY (model s.x) (model s.y))) :
    modelPoint (sumFromSlope r s (curve12.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y)))
      (nativeSum_onCurve r s rCurve sCurve notVertical) = modelPoint r rCurve + modelPoint s sCurve := by
  unfold modelPoint
  rw [WeierstrassCurve.Affine.Point.add_some notVertical]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨nativeSum_x _ _ _, nativeSum_y _ _ _⟩

theorem native_addSlope (r s : Point) (distinct : model r.x ≠ model s.x) :
    curve12.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y) = addSlope r s := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne distinct]
  unfold addSlope
  field_simp [sub_ne_zero.mpr distinct, sub_ne_zero.mpr distinct.symm]
  ring

theorem native_doubleSlope (point : Point) (nonzeroY : model point.y ≠ 0) :
    curve12.toAffine.slope (model point.x) (model point.x) (model point.y) (model point.y) = doubleSlope point := by
  have notNegative : model point.y ≠ curve12.toAffine.negY (model point.x) (model point.y) := by
    intro equal
    simp only [curve12_coefficients, WeierstrassCurve.Affine.negY, zero_mul, sub_zero] at equal
    have twice : (2 : Field) * model point.y = 0 := by linear_combination equal
    exact mul_ne_zero two_nonzero nonzeroY twice
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl notNegative]
  simp [curve12_coefficients, WeierstrassCurve.Affine.negY, doubleSlope, two_mul]

theorem native_normalizedLine (r s : Point) (rCurve : r.onCurve = true) (sCurve : s.onCurve = true)
    (notVertical : ¬(model r.x = model s.x ∧ model r.y = curve12.toAffine.negY (model s.x) (model s.y))) :
    normalizedLine (modelPoint r rCurve) (modelPoint s sCurve) =
      lineQuotient (model r.x) (model r.y)
        (curve12.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y))
        (model (sumFromSlope r s
          (curve12.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y))).x) := by
  change (if model r.x = model s.x ∧ model r.y = curve12.toAffine.negY (model s.x) (model s.y)
    then _ else _) = _
  rw [if_neg notVertical, nativeSum_x]

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.native12_equation
#print axioms LeanCrypto.Proofs.BN254Tate.nativeSum_x
#print axioms LeanCrypto.Proofs.BN254Tate.nativeSum_y
#print axioms LeanCrypto.Proofs.BN254Tate.nativeSum_onCurve
#print axioms LeanCrypto.Proofs.BN254Tate.nativeSum_modelPoint
#print axioms LeanCrypto.Proofs.BN254Tate.native_addSlope
#print axioms LeanCrypto.Proofs.BN254Tate.native_doubleSlope
#print axioms LeanCrypto.Proofs.BN254Tate.native_normalizedLine
