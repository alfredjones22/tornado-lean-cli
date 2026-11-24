import LeanCryptoProofs.ExplicitLineEvaluation
import LeanCryptoProofs.G1EvaluationModel

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

theorem opposite_line_product_fixed (x y : BN254Fp12.Field)
    (xReal : star x = x) (yReal : star y = y) (first second : twistSubgroup) :
    star (explicitLine x y first.val second.val * explicitLine x (-y) first.val second.val) =
      explicitLine x y first.val second.val * explicitLine x (-y) first.val second.val := by
  rcases first with ⟨first, firstTwist⟩
  rcases second with ⟨second, secondTwist⟩
  cases first with
  | zero => simp [explicitLine]
  | some x1 y1 h1 =>
    cases second with
    | zero => simp [explicitLine]
    | some x2 y2 h2 =>
      have inputs1 : star x1 = x1 ∧ star y1 = -y1 := firstTwist
      have inputs2 : star x2 = x2 ∧ star y2 = -y2 := secondTwist
      by_cases vertical : x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2
      · simp only [explicitLine, if_pos vertical, star_mul, star_sub, xReal, inputs1.1]
      · have slopeImaginary := star_curve_slope x1 x2 y1 y2 inputs1.1 inputs2.1 inputs1.2 inputs2.2
        have sumReal : star (curve12.toAffine.addX x1 x2 (curve12.toAffine.slope x1 x2 y1 y2)) =
            curve12.toAffine.addX x1 x2 (curve12.toAffine.slope x1 x2 y1 y2) := by
          simpa only [curve12_addX] using star_sumX x1 x2 _ inputs1.1 inputs2.1 slopeImaginary
        simp only [explicitLine, if_neg vertical, star_mul, star_div₀, star_sub, star_neg,
          xReal, yReal, inputs1.1, inputs1.2, slopeImaginary, sumReal]
        ring

def negativeNativeG1 (point : LeanCrypto.BN254.G1.Affine) : LeanCrypto.BN254.G1.Affine :=
  ⟨point.x, point.y.neg⟩

theorem negativeNativeG1_onCurve (point : LeanCrypto.BN254.G1.Affine) (onCurve : point.onCurve = true) :
    (negativeNativeG1 point).onCurve = true := by
  apply (BN254Fp.affine_onCurve_iff _).2
  simpa only [negativeNativeG1, BN254Fp.model_neg, neg_sq] using (BN254Fp.affine_onCurve_iff point).1 onCurve

theorem negativeNativeG1_x (point : LeanCrypto.BN254.G1.Affine) :
    BN254Fp12.model (embedG1 (negativeNativeG1 point)).x = BN254Fp12.model (embedG1 point).x := rfl

theorem negativeNativeG1_y (point : LeanCrypto.BN254.G1.Affine) :
    BN254Fp12.model (embedG1 (negativeNativeG1 point)).y = -BN254Fp12.model (embedG1 point).y := by
  change BN254Fp12.model (embedFp point.y.neg) = -BN254Fp12.model (embedFp point.y)
  rw [model_embedFp, model_embedFp, BN254Fp.model_neg, map_neg]

theorem reducedLine_negative (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup) :
    reducedLine evaluation onCurve first second *
      reducedLine (negativeNativeG1 evaluation) (negativeNativeG1_onCurve evaluation onCurve) first second = 1 := by
  simp only [reducedLine, evaluatedLine_explicit, negativeNativeG1_x, negativeNativeG1_y, ← mul_pow]
  apply star_fixed_reduces_one
  · apply mul_ne_zero
    · exact explicitLine_nonzero evaluation onCurve first second
    · have nz := explicitLine_nonzero (negativeNativeG1 evaluation)
        (negativeNativeG1_onCurve evaluation onCurve) first second
      simpa only [negativeNativeG1_x, negativeNativeG1_y] using nz
  · exact opposite_line_product_fixed _ _ (native_g1_x_real evaluation) (native_g1_y_real evaluation) first second

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.opposite_line_product_fixed
#print axioms LeanCrypto.Proofs.BN254Tate.negativeNativeG1_onCurve
#print axioms LeanCrypto.Proofs.BN254Tate.negativeNativeG1_x
#print axioms LeanCrypto.Proofs.BN254Tate.negativeNativeG1_y
#print axioms LeanCrypto.Proofs.BN254Tate.reducedLine_negative
