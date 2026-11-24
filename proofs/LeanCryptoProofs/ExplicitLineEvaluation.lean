import LeanCryptoProofs.ReducedLineCocycle

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

def explicitLine (x y : BN254Fp12.Field) : curve12.toAffine.Point → curve12.toAffine.Point → BN254Fp12.Field
  | .zero, _ => 1
  | _, .zero => 1
  | .some x1 y1 _, .some x2 y2 _ =>
    if x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2 then x - x1 else
      let slope := curve12.toAffine.slope x1 x2 y1 y2
      ((y - y1) - slope * (x - x1)) / (x - curve12.toAffine.addX x1 x2 slope)

theorem explicitLine_evaluates (evaluation : LeanCrypto.BN254.G1.Affine)
    (evaluationCurve : evaluation.onCurve = true) (first second : twistSubgroup) :
    Evaluates (embedG1 evaluation) (embedG1_onCurve evaluation evaluationCurve)
      (normalizedLine first.val second.val)
      (explicitLine (BN254Fp12.model (embedG1 evaluation).x)
        (BN254Fp12.model (embedG1 evaluation).y) first.val second.val) := by
  rcases first with ⟨first, firstTwist⟩
  rcases second with ⟨second, secondTwist⟩
  cases first with
  | zero => exact evaluates_one _ _
  | some x1 y1 h1 =>
    cases second with
    | zero => exact evaluates_one _ _
    | some x2 y2 h2 =>
      have inputs1 : star x1 = x1 ∧ star y1 = -y1 := firstTwist
      have inputs2 : star x2 = x2 ∧ star y2 = -y2 := secondTwist
      by_cases vertical : x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2
      · simp only [normalizedLine, explicitLine, if_pos vertical]
        exact verticalFunction_evaluates _ _ _
      · let slope := curve12.toAffine.slope x1 x2 y1 y2
        have h3 := WeierstrassCurve.Affine.nonsingular_add h1 h2 vertical
        have slopeImaginary := star_curve_slope x1 x2 y1 y2 inputs1.1 inputs2.1 inputs1.2 inputs2.2
        have y3Imaginary : star (curve12.toAffine.addY x1 x2 y1 slope) =
            -curve12.toAffine.addY x1 x2 y1 slope := by
          simpa only [curve12_addY] using star_sumY x1 x2 y1 slope inputs1.1 inputs2.1 inputs1.2 slopeImaginary
        have denominator := twist_vertical_evaluation_nonzero evaluation evaluationCurve
          (curve12.toAffine.addX x1 x2 slope) (curve12.toAffine.addY x1 x2 y1 slope) h3 y3Imaginary
        simp only [normalizedLine, explicitLine, if_neg vertical]
        exact lineQuotient_evaluates _ _ _ _ _ _ denominator

theorem evaluatedLine_explicit (evaluation : LeanCrypto.BN254.G1.Affine)
    (evaluationCurve : evaluation.onCurve = true) (first second : twistSubgroup) :
    evaluatedLine evaluation evaluationCurve first second =
      explicitLine (BN254Fp12.model (embedG1 evaluation).x)
        (BN254Fp12.model (embedG1 evaluation).y) first.val second.val :=
  evaluates_unique _ _ _ _ _ (evaluatedLine_evaluates evaluation evaluationCurve first second)
    (explicitLine_evaluates evaluation evaluationCurve first second)

theorem explicitLine_nonzero (evaluation : LeanCrypto.BN254.G1.Affine)
    (evaluationCurve : evaluation.onCurve = true) (first second : twistSubgroup) :
    explicitLine (BN254Fp12.model (embedG1 evaluation).x)
      (BN254Fp12.model (embedG1 evaluation).y) first.val second.val ≠ 0 := by
  rw [← evaluatedLine_explicit evaluation evaluationCurve first second]
  exact evaluatedLine_nonzero evaluation evaluationCurve first second

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.explicitLine_evaluates
#print axioms LeanCrypto.Proofs.BN254Tate.evaluatedLine_explicit
#print axioms LeanCrypto.Proofs.BN254Tate.explicitLine_nonzero
