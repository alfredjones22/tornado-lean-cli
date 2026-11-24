import LeanCryptoProofs.TwistGroup
import LeanCryptoProofs.LineFunctionStar
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate

def pointSign (point : curve12.toAffine.Point) : FunctionFieldˣ := if point = 0 then 1 else -1
def lineSign (first second : curve12.toAffine.Point) : FunctionFieldˣ :=
  pointSign first * pointSign second * (pointSign (first + second))⁻¹

theorem pointSign_zero : pointSign 0 = 1 := by rw [pointSign, if_pos rfl]

theorem pointSign_some (x y : BN254Fp12.Field) (h : curve12.toAffine.Nonsingular x y) :
    pointSign (.some x y h) = -1 := by
  have nonzero : (WeierstrassCurve.Affine.Point.some x y h : curve12.toAffine.Point) ≠ 0 := by
    intro impossible
    cases impossible
  rw [pointSign, if_neg nonzero]

theorem lineSign_zero_left (point : curve12.toAffine.Point) : lineSign 0 point = 1 := by
  rw [lineSign, pointSign_zero, zero_add]
  simp

theorem lineSign_zero_right (point : curve12.toAffine.Point) : lineSign point 0 = 1 := by
  rw [lineSign, pointSign_zero, add_zero]
  simp

theorem lineSign_finite_zero (x1 y1 x2 y2 : BN254Fp12.Field)
    (h1 : curve12.toAffine.Nonsingular x1 y1) (h2 : curve12.toAffine.Nonsingular x2 y2)
    (sumZero : WeierstrassCurve.Affine.Point.some x1 y1 h1 + .some x2 y2 h2 = 0) :
    lineSign (.some x1 y1 h1) (.some x2 y2 h2) = 1 := by
  rw [lineSign, pointSign_some, pointSign_some, sumZero, pointSign_zero]
  simp

theorem lineSign_finite_nonzero (x1 y1 x2 y2 : BN254Fp12.Field)
    (h1 : curve12.toAffine.Nonsingular x1 y1) (h2 : curve12.toAffine.Nonsingular x2 y2)
    (sumNonzero : WeierstrassCurve.Affine.Point.some x1 y1 h1 + .some x2 y2 h2 ≠ 0) :
    lineSign (.some x1 y1 h1) (.some x2 y2 h2) = -1 := by
  rw [lineSign, pointSign_some, pointSign_some]
  rw [pointSign, if_neg sumNonzero]
  simp

theorem lineSign_cocycle (first second third : curve12.toAffine.Point) :
    lineSign first second * lineSign (first + second) third =
      lineSign first (second + third) * lineSign second third := by
  simpa only [lineSign, add_assoc] using principal_cocycle_identity
    (pointSign first) (pointSign second) (pointSign third)
    (pointSign (first + second)) (pointSign (second + third))
    (pointSign (first + (second + third)))

theorem lineSign_symmetric (first second : curve12.toAffine.Point) :
    lineSign first second = lineSign second first := by
  simp only [lineSign, add_comm first second, mul_comm (pointSign first) (pointSign second)]

/-- The coefficient-star/Y-negation character of a normalized line is the
coboundary of pointSign, on the proved twist subgroup. -/
theorem normalizedLine_star (first second : curve12.toAffine.Point)
    (firstTwist : IsTwistPoint first) (secondTwist : IsTwistPoint second) :
    functionStar (normalizedLine first second) =
      (lineSign first second : FunctionField) * normalizedLine first second := by
  cases first with
  | zero =>
    change functionStar 1 = (lineSign 0 second : FunctionField) * 1
    rw [lineSign_zero_left]
    simp
  | some x1 y1 h1 =>
    cases second with
    | zero =>
      change functionStar 1 = (lineSign (.some x1 y1 h1) 0 : FunctionField) * 1
      rw [lineSign_zero_right]
      simp
    | some x2 y2 h2 =>
      have inputs1 : star x1 = x1 ∧ star y1 = -y1 := firstTwist
      have inputs2 : star x2 = x2 ∧ star y2 = -y2 := secondTwist
      by_cases vertical : x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2
      · have lineEq : normalizedLine (.some x1 y1 h1) (.some x2 y2 h2) = verticalFunction x1 := by
          change (if x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2 then _ else _) = _
          rw [if_pos vertical]
        have sign := lineSign_finite_zero x1 y1 x2 y2 h1 h2
          (WeierstrassCurve.Affine.Point.add_of_Y_eq vertical.1 vertical.2)
        rw [lineEq, functionStar_vertical x1 inputs1.1, sign]
        simp
      · let slope := curve12.toAffine.slope x1 x2 y1 y2
        let x3 := curve12.toAffine.addX x1 x2 slope
        have slopeImaginary : star slope = -slope := star_curve_slope x1 x2 y1 y2
          inputs1.1 inputs2.1 inputs1.2 inputs2.2
        have sumReal : star x3 = x3 := by
          simpa only [x3, curve12_addX] using star_sumX x1 x2 slope inputs1.1 inputs2.1 slopeImaginary
        have lineEq : normalizedLine (.some x1 y1 h1) (.some x2 y2 h2) = lineQuotient x1 y1 slope x3 := by
          change (if x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2 then _ else _) = _
          rw [if_neg vertical]
        have sumNonzero : WeierstrassCurve.Affine.Point.some x1 y1 h1 + .some x2 y2 h2 ≠ 0 := by
          rw [WeierstrassCurve.Affine.Point.add_some vertical]
          intro impossible
          cases impossible
        have sign := lineSign_finite_nonzero x1 y1 x2 y2 h1 h2 sumNonzero
        rw [lineEq, functionStar_quotient x1 y1 slope x3 inputs1.1 inputs1.2 slopeImaginary sumReal, sign]
        simp

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.pointSign_zero
#print axioms LeanCrypto.Proofs.BN254Tate.pointSign_some
#print axioms LeanCrypto.Proofs.BN254Tate.lineSign_zero_left
#print axioms LeanCrypto.Proofs.BN254Tate.lineSign_zero_right
#print axioms LeanCrypto.Proofs.BN254Tate.lineSign_finite_zero
#print axioms LeanCrypto.Proofs.BN254Tate.lineSign_finite_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.lineSign_cocycle
#print axioms LeanCrypto.Proofs.BN254Tate.lineSign_symmetric
#print axioms LeanCrypto.Proofs.BN254Tate.normalizedLine_star
