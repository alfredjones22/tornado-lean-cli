import LeanCryptoProofs.CurvePrincipal
open scoped nonZeroDivisors
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate

theorem principal_cocycle_identity {G : Type} [CommGroup G] (a b c d e f : G) :
    (a * b * d⁻¹) * (d * c * f⁻¹) = (a * e * f⁻¹) * (b * c * e⁻¹) := by
  calc
    _ = a * b * c * f⁻¹ := by simp only [mul_assoc, inv_mul_cancel_left]
    _ = (a * b * c * f⁻¹) * (e * e⁻¹) := by simp
    _ = _ := by ac_rfl

theorem principal_line_formula (first second : curve12.toAffine.Point) :
    principal (normalizedLine first second) (normalizedLine_nonzero first second) =
      (pointIdeal first * pointIdeal second) * (pointIdeal (first + second))⁻¹ := by
  calc
    _ = (principal (normalizedLine first second) (normalizedLine_nonzero first second) *
        pointIdeal (first + second)) * (pointIdeal (first + second))⁻¹ := by simp [mul_assoc]
    _ = _ := by rw [normalizedLine_principal_relation]

theorem line_principal_cocycle (first second third : curve12.toAffine.Point) :
    principal (normalizedLine first second) (normalizedLine_nonzero first second) *
      principal (normalizedLine (first + second) third) (normalizedLine_nonzero (first + second) third) =
    principal (normalizedLine first (second + third)) (normalizedLine_nonzero first (second + third)) *
      principal (normalizedLine second third) (normalizedLine_nonzero second third) := by
  rw [principal_line_formula, principal_line_formula, principal_line_formula, principal_line_formula]
  simpa only [add_assoc] using principal_cocycle_identity (pointIdeal first) (pointIdeal second)
    (pointIdeal third) (pointIdeal (first + second)) (pointIdeal (second + third))
      (pointIdeal (first + (second + third)))

def constantFunction (value : BN254Fp12.Field) : FunctionField :=
  algebraMap CoordinateRing FunctionField (algebraMap BN254Fp12.Field CoordinateRing value)

theorem principal_equal_constant (first second : FunctionField) (firstNonzero : first ≠ 0)
    (secondNonzero : second ≠ 0) (same : principal first firstNonzero = principal second secondNonzero) :
    ∃ constant : BN254Fp12.Field, constant ≠ 0 ∧ second = constantFunction constant * first := by
  have spans := congrArg (fun unit : FractionIdealˣ => (unit : FractionIdeal)) same
  change (principal first firstNonzero : FractionIdeal) = (principal second secondNonzero : FractionIdeal) at spans
  rw [principal_value, principal_value] at spans
  obtain ⟨unit, relation⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp spans
  obtain ⟨constant, nonzero, expression⟩ := coordinate_unit_constant (unit : CoordinateRing) unit.isUnit
  refine ⟨constant, nonzero, ?_⟩
  rw [Units.smul_def, Algebra.smul_def, expression] at relation
  exact relation.symm

theorem principal_product (first second : FunctionField) (firstNonzero : first ≠ 0)
    (secondNonzero : second ≠ 0) :
    principal (first * second) (mul_ne_zero firstNonzero secondNonzero) =
      principal first firstNonzero * principal second secondNonzero := by
  apply Units.val_injective
  simp only [Units.val_mul, principal_value, FractionalIdeal.spanSingleton_mul_spanSingleton]

/-- The line cocycle is already exact up to a nonzero constant, derived
from the mathematical curve's ideal relation. Its leading coefficient at
infinity must still identify this constant as one. -/
theorem line_cocycle_up_to_constant (first second third : curve12.toAffine.Point) :
    ∃ constant : BN254Fp12.Field, constant ≠ 0 ∧
      normalizedLine first (second + third) * normalizedLine second third = constantFunction constant *
        (normalizedLine first second * normalizedLine (first + second) third) := by
  apply principal_equal_constant _ _
    (mul_ne_zero (normalizedLine_nonzero _ _) (normalizedLine_nonzero _ _))
    (mul_ne_zero (normalizedLine_nonzero _ _) (normalizedLine_nonzero _ _))
  rw [principal_product, principal_product]
  exact line_principal_cocycle first second third

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.principal_line_formula
#print axioms LeanCrypto.Proofs.BN254Tate.principal_cocycle_identity
#print axioms LeanCrypto.Proofs.BN254Tate.line_principal_cocycle
#print axioms LeanCrypto.Proofs.BN254Tate.principal_equal_constant
#print axioms LeanCrypto.Proofs.BN254Tate.principal_product
#print axioms LeanCrypto.Proofs.BN254Tate.line_cocycle_up_to_constant
