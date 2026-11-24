import LeanCryptoProofs.G1GroupLaw
import LeanCryptoProofs.JacobianNormalization

namespace LeanCrypto.Proofs.BN254Group

open LeanCrypto.BN254.G1 LeanCrypto.Proofs.BN254Fp LeanCrypto.Proofs.BN254Jacobian

def affinePoint (point : Affine) (onCurve : point.onCurve = true) : curve.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some (model point.x) (model point.y)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      simpa [WeierstrassCurve.Affine.equation_iff, curve] using (affine_onCurve_iff point).1 onCurve))

theorem normalized_groupPoint (point : Jacobian) (finite : model point.z ≠ 0)
    (equation : ProjectiveEquation point) :
    groupPoint point = affinePoint (normalizedAffine point) (normalized_onCurve point finite equation) := by
  unfold groupPoint
  rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero
    (native_nonsingular point finite equation) finite]
  simp only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  unfold affinePoint
  congr 1
  · simp only [normalized_x, div_eq_mul_inv, inv_pow]
    rfl
  · simp only [normalized_y, div_eq_mul_inv, inv_pow]
    rfl

/-- Relation from the actual native optional affine result to the proved
mathematical group, with the native infinity sentinel mapped to zero. -/
def Represents (output : Option Affine) (mathematical : curve.toAffine.Point) : Prop :=
  match output with
  | none => mathematical = 0
  | some point => ∃ onCurve : point.onCurve = true, mathematical = affinePoint point onCurve

theorem toAffine_represents_groupPoint (point : Jacobian) (admitted : Admissible point) :
    ∃ output, point.toAffine = .ok output ∧ Represents output (groupPoint point) := by
  rcases admitted with infinite | ⟨finite, equation⟩
  · subst point
    exact ⟨none, toAffine_infinity_construct, infinity_groupPoint⟩
  · exact ⟨some (normalizedAffine point), toAffine_finite_construct point finite equation,
      normalized_onCurve point finite equation, normalized_groupPoint point finite equation⟩

/-- Every admitted native addition constructs an actual affine result
representing the sum in Mathlib's established elliptic-curve group. -/
theorem toAffine_add_represents_sum (left right : Jacobian)
    (leftAdmitted : Admissible left) (rightAdmitted : Admissible right) :
    ∃ output, (left.add right).toAffine = .ok output ∧
      Represents output (groupPoint left + groupPoint right) := by
  obtain ⟨output, constructed, represented⟩ := toAffine_represents_groupPoint (left.add right)
    (add_preserves_curve_certified left right leftAdmitted rightAdmitted)
  exact ⟨output, constructed, (add_groupPoint left right leftAdmitted rightAdmitted) ▸ represented⟩

theorem toAffine_double_represents_sum (point : Jacobian) (admitted : Admissible point) :
    ∃ output, point.double.toAffine = .ok output ∧
      Represents output (groupPoint point + groupPoint point) := by
  obtain ⟨output, constructed, represented⟩ := toAffine_represents_groupPoint point.double
    (double_preserves_curve_certified point admitted)
  exact ⟨output, constructed, (double_groupPoint point admitted) ▸ represented⟩

end LeanCrypto.Proofs.BN254Group

#print axioms LeanCrypto.Proofs.BN254Group.normalized_groupPoint
#print axioms LeanCrypto.Proofs.BN254Group.toAffine_represents_groupPoint
#print axioms LeanCrypto.Proofs.BN254Group.toAffine_add_represents_sum
#print axioms LeanCrypto.Proofs.BN254Group.toAffine_double_represents_sum
