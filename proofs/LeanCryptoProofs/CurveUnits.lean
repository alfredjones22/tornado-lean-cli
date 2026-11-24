import LeanCryptoProofs.CurveFunctionEvaluation
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open Polynomial

theorem coordinate_unit_constant (value : CoordinateRing) (unit : IsUnit value) :
    ∃ constant : BN254Fp12.Field, constant ≠ 0 ∧
      value = algebraMap BN254Fp12.Field CoordinateRing constant := by
  obtain ⟨p, q, expression⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq value
  have normUnit := unit.map (Algebra.norm (Polynomial BN254Fp12.Field))
  have normDegree := Polynomial.degree_eq_zero_of_isUnit normUnit
  rw [← expression, WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis] at normDegree
  have qZero : q = 0 := by
    by_contra nonzero
    have degreeNonnegative : (0 : WithBot Nat) ≤ q.degree := Polynomial.zero_le_degree_iff.mpr nonzero
    have positive : (0 : WithBot Nat) < 2 • q.degree + 3 := by
      calc
        0 < 3 := by decide
        _ ≤ 2 • q.degree + 3 := le_add_of_nonneg_left (nsmul_nonneg degreeNonnegative 2)
    have upper : 2 • q.degree + 3 ≤ 0 := by
      rw [← normDegree]
      exact le_max_right _ _
    exact not_lt_of_ge upper positive
  have simplified : p • (1 : CoordinateRing) = value := by
    simpa only [qZero, WeierstrassCurve.Affine.CoordinateRing.smul, Polynomial.C_0, map_zero,
      zero_mul, add_zero] using expression
  have pNorm : Algebra.norm (Polynomial BN254Fp12.Field) value = p ^ 2 := by
    rw [← expression, WeierstrassCurve.Affine.CoordinateRing.norm_smul_basis, qZero]
    simp
  have pUnit : IsUnit p := by
    rw [pNorm, pow_two] at normUnit
    exact isUnit_of_mul_isUnit_left normUnit
  have pConstant := Polynomial.eq_C_of_degree_eq_zero (Polynomial.degree_eq_zero_of_isUnit pUnit)
  have constantExpression : value = algebraMap BN254Fp12.Field CoordinateRing (p.coeff 0) := by
    rw [← simplified]
    conv_lhs => rw [pConstant]
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
    rfl
  refine ⟨p.coeff 0, ?_, constantExpression⟩
  intro zero
  have valueZero : value = 0 := by rw [constantExpression, zero, map_zero]
  exact unit.ne_zero valueZero

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.coordinate_unit_constant
