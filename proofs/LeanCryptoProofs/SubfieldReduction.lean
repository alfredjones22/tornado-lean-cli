import LeanCryptoProofs.TateFieldBridge
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate

def subfieldReductionExponent : Nat := finalExponent / (BN254Fp.P ^ 6 - 1)

theorem final_exponent_subfield_factor :
    finalExponent = (BN254Fp.P ^ 6 - 1) * subfieldReductionExponent := by decide +kernel

theorem subfield_reduces_one (value : BN254Fp6.Field) (nonzero : value ≠ 0) :
    (algebraMap BN254Fp6.Field BN254Fp12.Field value) ^ finalExponent = 1 := by
  rw [final_exponent_subfield_factor, pow_mul, ← map_pow, BN254Fp6.field_fermat value nonzero,
    map_one, one_pow]

theorem subfield_two_nonzero : (2 : BN254Fp6.Field) ≠ 0 := by
  intro zero
  have base : (2 : BN254Fp2.Field) ≠ 0 := by decide +kernel
  apply base
  apply (algebraMap BN254Fp2.Field BN254Fp6.Field).injective
  simpa only [map_ofNat, map_zero] using zero

theorem star_fixed_subfield (value : BN254Fp12.Field) (fixed : star value = value) :
    ∃ real : BN254Fp6.Field, value = algebraMap BN254Fp6.Field BN254Fp12.Field real := by
  have imaginary := congrArg QuadraticAlgebra.im fixed
  simp only [QuadraticAlgebra.im_star] at imaginary
  have twice : (2 : BN254Fp6.Field) * value.im = 0 := by linear_combination -imaginary
  have imaginaryZero := (mul_eq_zero.mp twice).resolve_left subfield_two_nonzero
  refine ⟨value.re, ?_⟩
  apply QuadraticAlgebra.ext
  · rfl
  · exact imaginaryZero

theorem star_fixed_reduces_one (value : BN254Fp12.Field) (nonzero : value ≠ 0)
    (fixed : star value = value) : value ^ finalExponent = 1 := by
  obtain ⟨real, representation⟩ := star_fixed_subfield value fixed
  have realNonzero : real ≠ 0 := by
    intro zero
    rw [representation, zero, map_zero] at nonzero
    exact nonzero rfl
  rw [representation]
  exact subfield_reduces_one real realNonzero

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.final_exponent_subfield_factor
#print axioms LeanCrypto.Proofs.BN254Tate.subfield_reduces_one
#print axioms LeanCrypto.Proofs.BN254Tate.subfield_two_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.star_fixed_subfield
#print axioms LeanCrypto.Proofs.BN254Tate.star_fixed_reduces_one
