import LeanCryptoProofs.ChordSection

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LineReciprocity

theorem section_vertical_product {F : Type} [Field F] (slope intercept coefficient : F)
    (roots : Section slope intercept coefficient) (x : F) :
    (roots.x0 - x) * (roots.x1 - x) * (roots.x2 - x) =
      (slope * x + intercept) ^ 2 - (x ^ 3 + coefficient) := by
  have sum := roots.sum
  have pairs := roots.pairs
  have product := roots.product
  linear_combination x ^ 2 * sum - x * pairs + product

theorem section_vertical_curve {F : Type} [Field F] (slope intercept coefficient : F)
    (roots : Section slope intercept coefficient) (x y : F) (equation : y ^ 2 = x ^ 3 + coefficient) :
    (roots.x0 - x) * (roots.x1 - x) * (roots.x2 - x) =
      (y - slope * x - intercept) * (-y - slope * x - intercept) := by
  rw [section_vertical_product, ← equation]
  ring

theorem section_quotient_reciprocity {F : Type} [Field F]
    (firstSlope firstIntercept secondSlope secondIntercept coefficient : F)
    (first : Section firstSlope firstIntercept coefficient)
    (second : Section secondSlope secondIntercept coefficient)
    (sumY : F) (sumOnCurve : sumY ^ 2 = second.x2 ^ 3 + coefficient)
    (sumNegative : -sumY = secondSlope * second.x2 + secondIntercept)
    (noPole : (first.x0 - second.x2) * (first.x1 - second.x2) * (first.x2 - second.x2) ≠ 0) :
    (((firstSlope - secondSlope) * first.x0 + (firstIntercept - secondIntercept)) /
        (first.x0 - second.x2)) *
      (((firstSlope - secondSlope) * first.x1 + (firstIntercept - secondIntercept)) /
        (first.x1 - second.x2)) *
      (((firstSlope - secondSlope) * first.x2 + (firstIntercept - secondIntercept)) /
        (first.x2 - second.x2)) =
    -(((secondSlope - firstSlope) * second.x0 + (secondIntercept - firstIntercept)) *
      ((secondSlope - firstSlope) * second.x1 + (secondIntercept - firstIntercept))) /
        (sumY - firstSlope * second.x2 - firstIntercept) := by
  let a := sumY - firstSlope * second.x2 - firstIntercept
  let b := -sumY - firstSlope * second.x2 - firstIntercept
  have denominator : (first.x0 - second.x2) * (first.x1 - second.x2) * (first.x2 - second.x2) = a * b :=
    section_vertical_curve _ _ _ first _ _ sumOnCurve
  have bNonzero : b ≠ 0 := by
    intro zero
    rw [denominator, zero, mul_zero] at noPole
    exact noPole rfl
  have third : (secondSlope - firstSlope) * second.x2 + (secondIntercept - firstIntercept) = b := by
    dsimp only [b]
    linear_combination -sumNegative
  have reciprocal := section_reciprocity firstSlope firstIntercept secondSlope secondIntercept coefficient first second
  dsimp only [evaluateOtherLine] at reciprocal
  rw [third] at reciprocal
  rw [div_mul_div_comm, div_mul_div_comm, reciprocal, denominator]
  change -(_ * _ * b) / (a * b) = -(_ * _) / a
  rw [← neg_mul, mul_div_mul_right _ _ bNonzero]

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.section_vertical_product
#print axioms LeanCrypto.Proofs.BN254Tate.section_vertical_curve
#print axioms LeanCrypto.Proofs.BN254Tate.section_quotient_reciprocity
