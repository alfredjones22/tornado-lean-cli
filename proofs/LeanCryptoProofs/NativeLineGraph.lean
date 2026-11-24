import LeanCryptoProofs.NativeLineGeometry
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing BN254Fp12

def Represents12 (result : Option Point) (meaning : curve12.toAffine.Point) : Prop :=
  match result with
  | none => meaning = 0
  | some point => ∃ onCurve : point.onCurve = true, meaning = modelPoint point onCurve

theorem nativePoint_model_ext {left right : Point} (x : model left.x = model right.x)
    (y : model left.y = model right.y) : left = right := by
  have sameX := model_injective x
  have sameY := model_injective y
  cases left
  cases right
  cases sameX
  cases sameY
  rfl

theorem nativeLine_finite_graph (r s : Point) (rCurve : r.onCurve = true) (sCurve : s.onCurve = true)
    (rTwist : IsTwistPoint (modelPoint r rCurve)) (sTwist : IsTwistPoint (modelPoint s sCurve))
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true)
    (notVertical : ¬(model r.x = model s.x ∧ model r.y = curve12.toAffine.negY (model s.x) (model s.y))) :
    ∃ factor : Fp12,
      nativeLineAndSum r s (embedG1 evaluation) = .ok (factor, some
        (sumFromSlope r s (curve12.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y)))) ∧
      Represents12 (some (sumFromSlope r s
        (curve12.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y))))
        (modelPoint r rCurve + modelPoint s sCurve) ∧
      Evaluates (embedG1 evaluation) (embedG1_onCurve evaluation evaluationCurve)
        (normalizedLine (modelPoint r rCurve) (modelPoint s sCurve)) (model factor) := by
  let slope := curve12.toAffine.slope (model r.x) (model s.x) (model r.y) (model s.y)
  let sum := sumFromSlope r s slope
  have rInputs : star (model r.x) = model r.x ∧ star (model r.y) = -model r.y := rTwist
  have sInputs : star (model s.x) = model s.x ∧ star (model s.y) = -model s.y := sTwist
  have sumCurve : sum.onCurve = true := nativeSum_onCurve r s rCurve sCurve notVertical
  have sumNonsingular : curve12.toAffine.Nonsingular (model sum.x) (model sum.y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (native12_equation sum sumCurve)
  have slopeImaginary : star slope = -slope :=
    star_curve_slope _ _ _ _ rInputs.1 sInputs.1 rInputs.2 sInputs.2
  have sumImaginary : star (model sum.y) = -model sum.y := by
    simpa only [sum, sumFromSlope_y] using
      star_sumY _ _ _ slope rInputs.1 sInputs.1 rInputs.2 slopeImaginary
  have vertical : model (embedG1 evaluation).x - model sum.x ≠ 0 :=
    twist_vertical_evaluation_nonzero evaluation evaluationCurve _ _ sumNonsingular sumImaginary
  have line : lineValue r (embedG1 evaluation) slope ≠ 0 :=
    twist_line_evaluation_nonzero evaluation evaluationCurve _ _ slope rInputs.1 rInputs.2 slopeImaginary
  let factor := encode (lineValue r (embedG1 evaluation) slope / (model (embedG1 evaluation).x - model sum.x))
  have constructed : nativeLineAndSum r s (embedG1 evaluation) = .ok (factor, some sum) := by
    by_cases sameX : model r.x = model s.x
    · have notNegative : model r.y ≠ -model s.y := by
        intro equal
        exact notVertical ⟨sameX, by simpa [curve12_coefficients, WeierstrassCurve.Affine.negY] using equal⟩
      have squares : model r.y ^ 2 = model s.y ^ 2 := by
        rw [(native_onCurve_iff r).1 rCurve, (native_onCurve_iff s).1 sCurve, sameX]
      have factored : (model r.y - model s.y) * (model r.y + model s.y) = 0 := by
        calc
          _ = model r.y ^ 2 - model s.y ^ 2 := by ring
          _ = 0 := by rw [squares]; ring
      have sameY : model r.y = model s.y := by
        rcases mul_eq_zero.mp factored with first | second
        · exact sub_eq_zero.mp first
        · exact False.elim (notNegative (eq_neg_of_add_eq_zero_left second))
      have same := nativePoint_model_ext sameX sameY
      subst s
      have nonzeroY : model r.y ≠ 0 := by intro zero; apply notNegative; simp [zero]
      have slopeEq : slope = doubleSlope r := native_doubleSlope r nonzeroY
      have denominator : model (embedG1 evaluation).x - model (sumFromSlope r r (doubleSlope r)).x ≠ 0 := by
        simpa only [sum, slopeEq] using vertical
      have numerator : lineValue r (embedG1 evaluation) (doubleSlope r) ≠ 0 := by
        simpa only [slopeEq] using line
      have actual := line_double_construct r (embedG1 evaluation) nonzeroY denominator numerator
      simpa only [← slopeEq] using actual
    · have slopeEq : slope = addSlope r s := native_addSlope r s sameX
      have denominator : model (embedG1 evaluation).x - model (sumFromSlope r s (addSlope r s)).x ≠ 0 := by
        simpa only [sum, slopeEq] using vertical
      have numerator : lineValue r (embedG1 evaluation) (addSlope r s) ≠ 0 := by
        simpa only [slopeEq] using line
      have actual := line_add_construct r s (embedG1 evaluation) sameX denominator numerator
      simpa only [← slopeEq] using actual
  refine ⟨factor, constructed, ⟨sumCurve, (nativeSum_modelPoint r s rCurve sCurve notVertical).symm⟩, ?_⟩
  rw [native_normalizedLine r s rCurve sCurve notVertical]
  simp only [factor, model_encode]
  exact lineQuotient_evaluates _ _ _ _ _ _ vertical

theorem nativeLine_graph (r s : Point) (rCurve : r.onCurve = true) (sCurve : s.onCurve = true)
    (rTwist : IsTwistPoint (modelPoint r rCurve)) (sTwist : IsTwistPoint (modelPoint s sCurve))
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true) :
    ∃ (factor : Fp12) (sum : Option Point),
      nativeLineAndSum r s (embedG1 evaluation) = .ok (factor, sum) ∧
      Represents12 sum (modelPoint r rCurve + modelPoint s sCurve) ∧
      Evaluates (embedG1 evaluation) (embedG1_onCurve evaluation evaluationCurve)
        (normalizedLine (modelPoint r rCurve) (modelPoint s sCurve)) (model factor) := by
  by_cases vertical : model r.x = model s.x ∧ model r.y = curve12.toAffine.negY (model s.x) (model s.y)
  · have rInputs : star (model r.x) = model r.x ∧ star (model r.y) = -model r.y := rTwist
    have nonsingular := WeierstrassCurve.Affine.equation_iff_nonsingular.mp (native12_equation r rCurve)
    have denominator := twist_vertical_evaluation_nonzero evaluation evaluationCurve _ _ nonsingular rInputs.2
    have negative : model r.y = -model s.y := by
      simpa [curve12_coefficients, WeierstrassCurve.Affine.negY] using vertical.2
    have constructed := line_vertical_construct r s (embedG1 evaluation) vertical.1 negative denominator
    have sumZero : modelPoint r rCurve + modelPoint s sCurve = 0 := by
      unfold modelPoint
      exact WeierstrassCurve.Affine.Point.add_of_Y_eq vertical.1 vertical.2
    have lineEq : normalizedLine (modelPoint r rCurve) (modelPoint s sCurve) = verticalFunction (model r.x) := by
      change (if model r.x = model s.x ∧ model r.y = curve12.toAffine.negY (model s.x) (model s.y)
        then _ else _) = _
      rw [if_pos vertical]
    refine ⟨(embedG1 evaluation).x.sub r.x, none, constructed, sumZero, ?_⟩
    rw [lineEq, model_sub]
    exact verticalFunction_evaluates _ _ _
  · obtain ⟨factor, constructed, represented, evaluated⟩ :=
      nativeLine_finite_graph r s rCurve sCurve rTwist sTwist evaluation evaluationCurve vertical
    exact ⟨factor, _, constructed, represented, evaluated⟩

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.nativePoint_model_ext
#print axioms LeanCrypto.Proofs.BN254Tate.nativeLine_finite_graph
#print axioms LeanCrypto.Proofs.BN254Tate.nativeLine_graph
