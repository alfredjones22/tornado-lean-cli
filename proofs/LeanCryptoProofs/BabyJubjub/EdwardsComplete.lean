import LeanCryptoProofs.CertifiedFields
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjubComplete

variable {F : Type*} [Field F]

def Edwards (a d x y : F) : Prop := a * x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2

theorem square_of_inverse_product (d z : F) (identity : d * z ^ 2 = 1) : IsSquare d := by
  have nonzero : z ≠ 0 := by intro zero; simp [zero] at identity
  have equal : d = (z ^ 2)⁻¹ := (mul_eq_one_iff_eq_inv₀ (pow_ne_zero 2 nonzero)).1 identity
  rw [← inv_pow] at equal
  exact ⟨z⁻¹, by simpa only [pow_two] using equal⟩

/-- Complete Edwards addition excludes both denominator signs by field
algebra, without point counting, sampled tests or a runtime-success premise. -/
theorem no_signed_denominator (a d x1 y1 x2 y2 epsilon : F)
    (first : Edwards a d x1 y1) (second : Edwards a d x2 y2)
    (squareA : IsSquare a) (nonsquareD : ¬ IsSquare d) (sign : epsilon ^ 2 = 1) :
    d * x1 * x2 * y1 * y2 ≠ epsilon := by
  intro denominator
  have epsilonNonzero : epsilon ≠ 0 := by intro zero; simp [zero] at sign
  have factor : (x1 * y2 - epsilon * x2 * y1) *
      (a * x1 * x2 - epsilon * y1 * y2) = 0 := by
    calc
      _ = x2*y2*(a*x1^2+y1^2)-epsilon*x1*y1*(a*x2^2+y2^2)+
          (epsilon^2-1)*x2*y1^2*y2 := by ring
      _ = x2*y2*(1+d*x1^2*y1^2)-epsilon*x1*y1*(1+d*x2^2*y2^2) := by
        rw [show a*x1^2+y1^2=1+d*x1^2*y1^2 from first,
          show a*x2^2+y2^2=1+d*x2^2*y2^2 from second, sign]
        ring
      _ = x2*y2*(1-epsilon*(d*x1*x2*y1*y2))+
          x1*y1*(d*x1*x2*y1*y2-epsilon) := by ring
      _ = 0 := by rw [denominator]; simp only [← pow_two, sign]; ring
  rcases mul_eq_zero.mp factor with firstFactor | secondFactor
  · have equal : x1*y2=epsilon*x2*y1 := sub_eq_zero.mp firstFactor
    have identity : d*(x2*y1)^2=1 := by
      apply mul_left_cancel₀ epsilonNonzero
      calc
        epsilon*(d*(x2*y1)^2) = d*(epsilon*x2*y1)*(x2*y1) := by ring
        _ = d*(x1*y2)*(x2*y1) := by rw [← equal]
        _ = d*x1*x2*y1*y2 := by ring
        _ = epsilon*1 := by rw [denominator]; ring
    exact nonsquareD (square_of_inverse_product d (x2*y1) identity)
  · have equal : a*x1*x2=epsilon*y1*y2 := sub_eq_zero.mp secondFactor
    have identity : d*a*(x1*x2)^2=1 := by
      apply mul_left_cancel₀ epsilonNonzero
      calc
        epsilon*(d*a*(x1*x2)^2) = d*(a*x1*x2)*(epsilon*x1*x2) := by ring
        _ = d*(epsilon*y1*y2)*(epsilon*x1*x2) := by rw [equal]
        _ = epsilon^2*(d*x1*x2*y1*y2) := by ring
        _ = d*x1*x2*y1*y2 := by rw [sign]; ring
        _ = epsilon*1 := by rw [denominator]; ring
    obtain ⟨root, rootSquare⟩ := squareA
    have combined : d*(root*(x1*x2))^2=1 := by
      rw [rootSquare] at identity
      convert identity using 1; ring
    exact nonsquareD (square_of_inverse_product d (root*(x1*x2)) combined)

theorem complete_denominators (a d x1 y1 x2 y2 : F)
    (first : Edwards a d x1 y1) (second : Edwards a d x2 y2)
    (squareA : IsSquare a) (nonsquareD : ¬ IsSquare d) :
    1 + d*x1*x2*y1*y2 ≠ 0 ∧ 1 - d*x1*x2*y1*y2 ≠ 0 := by
  constructor
  · intro zero
    have bad : d*x1*x2*y1*y2 = -1 := by
      exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm, add_assoc] using zero)
    exact no_signed_denominator a d x1 y1 x2 y2 (-1) first second squareA nonsquareD (by ring) bad
  · intro zero
    have bad : d*x1*x2*y1*y2 = 1 := by
      exact (sub_eq_zero.mp zero).symm
    exact no_signed_denominator a d x1 y1 x2 y2 1 first second squareA nonsquareD (by ring) bad

end LeanCrypto.Proofs.BabyJubjubComplete
#print axioms LeanCrypto.Proofs.BabyJubjubComplete.square_of_inverse_product
#print axioms LeanCrypto.Proofs.BabyJubjubComplete.no_signed_denominator
#print axioms LeanCrypto.Proofs.BabyJubjubComplete.complete_denominators
