import LeanCryptoProofs.SectionEvaluation
import LeanCryptoProofs.ExplicitLineEvaluation
import LeanCryptoProofs.NativeG1Chord

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace LeanCrypto.Proofs.BN254Tate
open LineReciprocity

def chordAt (slope intercept : BN254Fp12.Field) : curve12.toAffine.Point → BN254Fp12.Field
  | .zero => 1
  | .some x y _ => y - slope * x - intercept

theorem section_line_nonzero (slope intercept : BN254Fp12.Field) (roots : Section slope intercept 3)
    (x y : BN254Fp12.Field) (equation : y ^ 2 = x ^ 3 + 3)
    (separated : (roots.x0 - x) * (roots.x1 - x) * (roots.x2 - x) ≠ 0) :
    y - slope * x - intercept ≠ 0 := by
  intro zero
  apply separated
  rw [section_vertical_curve _ _ _ roots x y equation, zero, zero_mul]

theorem negative_final_power (value : BN254Fp12.Field) : (-value) ^ finalExponent = value ^ finalExponent := by
  have negativeOne : (-1 : BN254Fp12.Field) ^ finalExponent = 1 := by
    apply star_fixed_reduces_one
    · exact neg_ne_zero.mpr one_ne_zero
    · simp
  rw [show -value = (-1 : BN254Fp12.Field) * value by ring, mul_pow, negativeOne, one_mul]

/-- Reciprocity on one complete chord section. Separation is an independent
geometric condition on its three roots, not an evaluation or checker result. -/
theorem section_explicit_reduced_product (slope intercept : BN254Fp12.Field)
    (roots : Section slope intercept 3)
    (separated : ∀ (x y : BN254Fp12.Field) (h : curve12.toAffine.Nonsingular x y),
      IsTwistPoint (.some x y h) →
        (roots.x0 - x) * (roots.x1 - x) * (roots.x2 - x) ≠ 0)
    (first second : twistSubgroup) :
    (explicitLine roots.x0 (slope * roots.x0 + intercept) first.val second.val *
      explicitLine roots.x1 (slope * roots.x1 + intercept) first.val second.val *
      explicitLine roots.x2 (slope * roots.x2 + intercept) first.val second.val) ^ finalExponent =
      (chordAt slope intercept first.val * chordAt slope intercept second.val /
        chordAt slope intercept (first.val + second.val)) ^ finalExponent := by
  have noZero (point : twistSubgroup) : chordAt slope intercept point.val ≠ 0 := by
    rcases point with ⟨point, twist⟩
    cases point with
    | zero => exact one_ne_zero
    | some x y h =>
      apply section_line_nonzero slope intercept roots x y
      · have eq := (WeierstrassCurve.Affine.equation_iff _ _).1 h.left
        simpa only [curve12_coefficients, zero_mul, add_zero] using eq
      · exact separated x y h twist
  rcases first with ⟨first, firstTwist⟩
  rcases second with ⟨second, secondTwist⟩
  cases first with
  | zero =>
    change (1 * 1 * 1) ^ finalExponent = (1 * chordAt slope intercept second / chordAt slope intercept second) ^ finalExponent
    rw [one_mul, one_mul, one_mul, div_self (noZero ⟨second, secondTwist⟩)]
  | some x1 y1 h1 =>
    cases second with
    | zero =>
      change (1 * 1 * 1) ^ finalExponent =
        (chordAt slope intercept (.some x1 y1 h1) * 1 / chordAt slope intercept (.some x1 y1 h1)) ^ finalExponent
      rw [one_mul, one_mul, mul_one, div_self (noZero ⟨.some x1 y1 h1, firstTwist⟩)]
    | some x2 y2 h2 =>
      by_cases vertical : x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2
      · have sumZero : WeierstrassCurve.Affine.Point.some x1 y1 h1 + .some x2 y2 h2 = 0 :=
          WeierstrassCurve.Affine.Point.add_of_Y_eq vertical.1 vertical.2
        simp only [explicitLine, if_pos vertical, sumZero, chordAt, div_one]
        have equation : y1 ^ 2 = x1 ^ 3 + 3 := by
          have eq := (WeierstrassCurve.Affine.equation_iff _ _).1 h1.left
          simpa only [curve12_coefficients, zero_mul, add_zero] using eq
        have y2Eq : y2 = -y1 := by
          have eq := vertical.2
          simp only [WeierstrassCurve.Affine.negY, curve12_coefficients, zero_mul, sub_zero] at eq
          exact eq_neg_of_add_eq_zero_right (by linear_combination eq)
        rw [section_vertical_curve _ _ _ roots x1 y1 equation, ← vertical.1, y2Eq]
      · let mu := chordSlope x1 x2 y1 y2
        let eta := chordIntercept x1 x2 y1 y2
        let other := chordSection x1 x2 y1 y2 h1.left h2.left vertical
        let sx := curve12.toAffine.addX x1 x2 mu
        let sy := curve12.toAffine.addY x1 x2 y1 mu
        have h3 : curve12.toAffine.Nonsingular sx sy :=
          WeierstrassCurve.Affine.nonsingular_add h1 h2 vertical
        have sumTwist : IsTwistPoint (.some sx sy h3) := by
          have twist := twistPoint_add (.some x1 y1 h1) (.some x2 y2 h2) firstTwist secondTwist
          rwa [WeierstrassCurve.Affine.Point.add_some vertical] at twist
        have sumEquation : sy ^ 2 = sx ^ 3 + 3 := by
          have eq := (WeierstrassCurve.Affine.equation_iff _ _).1 h3.left
          simpa only [curve12_coefficients, zero_mul, add_zero] using eq
        have sumNegative : -sy = mu * sx + eta := by
          dsimp only [sy, sx, eta, mu, chordIntercept]
          rw [curve12_addY, curve12_addX]
          ring
        have helper := section_quotient_reciprocity slope intercept mu eta 3 roots other sy
          sumEquation sumNegative (separated sx sy h3 sumTwist)
        have otherX0 : other.x0 = x1 := rfl
        have otherX1 : other.x1 = x2 := rfl
        have otherX2 : other.x2 = sx := rfl
        rw [otherX0, otherX1, otherX2] at helper
        have numerator (x : BN254Fp12.Field) :
            (slope - mu) * x + (intercept - eta) = (slope * x + intercept - y1) - mu * (x - x1) := by
          dsimp only [eta, chordIntercept, mu]
          ring
        have oppositeFirst : (mu - slope) * x1 + (eta - intercept) = y1 - slope * x1 - intercept := by
          dsimp only [eta, chordIntercept, mu]
          ring
        have oppositeSecond : (mu - slope) * x2 + (eta - intercept) = y2 - slope * x2 - intercept := by
          have line := chord_second_on_line x1 x2 y1 y2 h1.left h2.left vertical
          change y2 = mu * x2 + eta at line
          linear_combination -line
        rw [numerator, numerator, numerator, oppositeFirst, oppositeSecond] at helper
        have equality :
            explicitLine roots.x0 (slope * roots.x0 + intercept) (.some x1 y1 h1) (.some x2 y2 h2) *
              explicitLine roots.x1 (slope * roots.x1 + intercept) (.some x1 y1 h1) (.some x2 y2 h2) *
              explicitLine roots.x2 (slope * roots.x2 + intercept) (.some x1 y1 h1) (.some x2 y2 h2) =
            -(chordAt slope intercept (.some x1 y1 h1) * chordAt slope intercept (.some x2 y2 h2) /
              chordAt slope intercept (.some sx sy h3)) := by
          simp only [explicitLine, if_neg vertical, chordAt]
          simpa only [sx, mu, chordSlope, neg_div] using helper
        rw [equality, negative_final_power, WeierstrassCurve.Affine.Point.add_some vertical]
        rfl

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.section_line_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.negative_final_power
#print axioms LeanCrypto.Proofs.BN254Tate.section_explicit_reduced_product
