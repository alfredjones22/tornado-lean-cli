import LeanCryptoProofs.TateTwistClosure
import LeanCryptoProofs.G2NormalizationGroupLaw
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 BN254Fp2 BN254G2Group

theorem affine_equation (point : Affine) (admitted : point.onCurve = true) :
    curve.toAffine.Equation (model point.x) (model point.y) := by
  simpa [WeierstrassCurve.Affine.equation_iff, curve] using (affine_onCurve_iff point).1 admitted

theorem g2Sum_x (r s : Affine) (slope : BN254Fp2.Field) :
    model (g2SumFromSlope r s slope).x = curve.toAffine.addX (model r.x) (model s.x) slope := by
  simp [g2SumFromSlope, WeierstrassCurve.Affine.addX, curve]

theorem g2Sum_y (r s : Affine) (slope : BN254Fp2.Field) :
    model (g2SumFromSlope r s slope).y = curve.toAffine.addY (model r.x) (model s.x) (model r.y) slope := by
  simp [g2SumFromSlope, WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, curve]
  ring

theorem g2Sum_admitted (r s : Affine) (rCurve : r.onCurve = true) (sCurve : s.onCurve = true)
    (notVertical : ¬(model r.x = model s.x ∧ model r.y = curve.toAffine.negY (model s.x) (model s.y))) :
    (g2SumFromSlope r s (curve.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y))).onCurve = true := by
  apply (affine_onCurve_iff _).2
  have equation := WeierstrassCurve.Affine.equation_add (affine_equation r rCurve)
    (affine_equation s sCurve) notVertical
  have converted := (WeierstrassCurve.Affine.equation_iff _ _).1 equation
  rw [← g2Sum_x, ← g2Sum_y] at converted
  simpa [curve] using converted

theorem g2Sum_represents (r s : Affine) (rCurve : r.onCurve = true) (sCurve : s.onCurve = true)
    (notVertical : ¬(model r.x = model s.x ∧ model r.y = curve.toAffine.negY (model s.x) (model s.y))) :
    affinePoint (g2SumFromSlope r s (curve.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y)))
      (g2Sum_admitted r s rCurve sCurve notVertical) = affinePoint r rCurve + affinePoint s sCurve := by
  unfold affinePoint
  rw [WeierstrassCurve.Affine.Point.add_some notVertical]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨g2Sum_x _ _ _, g2Sum_y _ _ _⟩

theorem addition_slope (r s : Affine) (distinct : model r.x ≠ model s.x) :
    curve.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y) =
      (model s.y - model r.y) / (model s.x - model r.x) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne distinct]
  field_simp [sub_ne_zero.mpr distinct, sub_ne_zero.mpr distinct.symm]
  ring

theorem doubling_slope (point : Affine) (nonzeroY : model point.y ≠ 0) :
    curve.toAffine.slope (model point.x) (model point.x) (model point.y) (model point.y) =
      3 * model point.x ^ 2 / (2 * model point.y) := by
  have notNegative : model point.y ≠ curve.toAffine.negY (model point.x) (model point.y) := by
    intro equal
    simp only [curve, WeierstrassCurve.Affine.negY,
      zero_mul, sub_zero] at equal
    have twice : (2 : BN254Fp2.Field) * model point.y = 0 := by linear_combination equal
    exact mul_ne_zero (by decide +kernel) nonzeroY twice
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl notNegative]
  simp [curve, WeierstrassCurve.Affine.negY, two_mul]

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.affine_equation
#print axioms LeanCrypto.Proofs.BN254Tate.g2Sum_x
#print axioms LeanCrypto.Proofs.BN254Tate.g2Sum_y
#print axioms LeanCrypto.Proofs.BN254Tate.g2Sum_admitted
#print axioms LeanCrypto.Proofs.BN254Tate.g2Sum_represents
#print axioms LeanCrypto.Proofs.BN254Tate.addition_slope
#print axioms LeanCrypto.Proofs.BN254Tate.doubling_slope
