import LeanCryptoProofs.TwistLineStar
import LeanCryptoProofs.NativeLineFunction
import LeanCryptoProofs.FpCoordinateNonzero
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

theorem native_g1_x_real (point : LeanCrypto.BN254.G1.Affine) :
    star (BN254Fp12.model (embedG1 point).x) = BN254Fp12.model (embedG1 point).x := by
  change star (BN254Fp12.model (embedFp point.x)) = BN254Fp12.model (embedFp point.x)
  simp only [model_embedFp]
  apply QuadraticAlgebra.ext <;> simp [fpHom, fp2Hom]

theorem native_g1_y_real (point : LeanCrypto.BN254.G1.Affine) :
    star (BN254Fp12.model (embedG1 point).y) = BN254Fp12.model (embedG1 point).y := by
  change star (BN254Fp12.model (embedFp point.y)) = BN254Fp12.model (embedFp point.y)
  simp only [model_embedFp]
  apply QuadraticAlgebra.ext <;> simp [fpHom, fp2Hom]

theorem native_g1_y_nonzero (point : LeanCrypto.BN254.G1.Affine) (onCurve : point.onCurve = true) :
    BN254Fp12.model (embedG1 point).y ≠ 0 := by
  change BN254Fp12.model (embedFp point.y) ≠ 0
  rw [model_embedFp]
  intro zero
  apply BN254G1Coordinates.affine_y_nonzero point onCurve
  apply fpHom.injective
  simpa only [map_zero] using zero

theorem real_imaginary_square_distinct (real imaginary : BN254Fp12.Field)
    (realNonzero : real ≠ 0) (realFixed : star real = real) (imaginaryNeg : star imaginary = -imaginary) :
    real ^ 2 ≠ imaginary ^ 2 := by
  intro square
  have factored : (imaginary - real) * (imaginary + real) = 0 := by
    calc
      _ = imaginary ^ 2 - real ^ 2 := by ring
      _ = 0 := by rw [square]; ring
  rcases mul_eq_zero.mp factored with difference | sum
  · have equal := sub_eq_zero.mp difference
    rw [equal, realFixed] at imaginaryNeg
    have twice : (2 : BN254Fp12.Field) * real = 0 := by linear_combination imaginaryNeg
    exact mul_ne_zero two_nonzero realNonzero twice
  · have equal := eq_neg_of_add_eq_zero_left sum
    rw [equal, star_neg, realFixed, neg_neg] at imaginaryNeg
    have twice : (2 : BN254Fp12.Field) * real = 0 := by linear_combination -imaginaryNeg
    exact mul_ne_zero two_nonzero realNonzero twice

theorem twist_vertical_evaluation_nonzero (evaluation : LeanCrypto.BN254.G1.Affine)
    (evaluationCurve : evaluation.onCurve = true) (x y : BN254Fp12.Field)
    (onCurve : curve12.toAffine.Nonsingular x y) (imaginaryY : star y = -y) :
    BN254Fp12.model (embedG1 evaluation).x - x ≠ 0 := by
  intro zero
  have equal := sub_eq_zero.mp zero
  have firstEquation := (native_onCurve_iff _).1 (embedG1_onCurve evaluation evaluationCurve)
  have secondEquation := (WeierstrassCurve.Affine.equation_iff _ _).1 onCurve.left
  simp only [curve12_coefficients, zero_mul, add_zero] at secondEquation
  have square : BN254Fp12.model (embedG1 evaluation).y ^ 2 = y ^ 2 := by
    rw [firstEquation, equal, secondEquation]
  exact real_imaginary_square_distinct _ _ (native_g1_y_nonzero evaluation evaluationCurve)
    (native_g1_y_real evaluation) imaginaryY square

theorem twist_line_evaluation_nonzero (evaluation : LeanCrypto.BN254.G1.Affine)
    (evaluationCurve : evaluation.onCurve = true) (x y slope : BN254Fp12.Field)
    (realX : star x = x) (imaginaryY : star y = -y) (imaginarySlope : star slope = -slope) :
    (BN254Fp12.model (embedG1 evaluation).y - y) -
      slope * (BN254Fp12.model (embedG1 evaluation).x - x) ≠ 0 := by
  intro zero
  have conjugate := congrArg star zero
  simp only [star_sub, star_mul, star_zero, native_g1_y_real, native_g1_x_real,
    realX, imaginaryY, imaginarySlope] at conjugate
  have twice : (2 : BN254Fp12.Field) * BN254Fp12.model (embedG1 evaluation).y = 0 := by
    linear_combination zero + conjugate
  exact mul_ne_zero two_nonzero (native_g1_y_nonzero evaluation evaluationCurve) twice

theorem normalizedLine_evaluates (evaluation : LeanCrypto.BN254.G1.Affine)
    (evaluationCurve : evaluation.onCurve = true) (first second : curve12.toAffine.Point)
    (firstTwist : IsTwistPoint first) (secondTwist : IsTwistPoint second) :
    ∃ value : BN254Fp12.Field, value ≠ 0 ∧
      Evaluates (embedG1 evaluation) (embedG1_onCurve evaluation evaluationCurve)
        (normalizedLine first second) value := by
  cases first with
  | zero =>
    refine ⟨1, one_ne_zero, ?_⟩
    exact evaluates_one _ _
  | some x1 y1 h1 =>
    cases second with
    | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      exact evaluates_one _ _
    | some x2 y2 h2 =>
      have inputs1 : star x1 = x1 ∧ star y1 = -y1 := firstTwist
      have inputs2 : star x2 = x2 ∧ star y2 = -y2 := secondTwist
      by_cases vertical : x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2
      · have lineEq : normalizedLine (.some x1 y1 h1) (.some x2 y2 h2) = verticalFunction x1 := by
          change (if x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2 then _ else _) = _
          rw [if_pos vertical]
        refine ⟨BN254Fp12.model (embedG1 evaluation).x - x1,
          twist_vertical_evaluation_nonzero evaluation evaluationCurve x1 y1 h1 inputs1.2, ?_⟩
        rw [lineEq]
        exact verticalFunction_evaluates _ _ _
      · let slope := curve12.toAffine.slope x1 x2 y1 y2
        let x3 := curve12.toAffine.addX x1 x2 slope
        let y3 := curve12.toAffine.addY x1 x2 y1 slope
        have h3 : curve12.toAffine.Nonsingular x3 y3 :=
          WeierstrassCurve.Affine.nonsingular_add h1 h2 vertical
        have slopeImaginary : star slope = -slope :=
          star_curve_slope x1 x2 y1 y2 inputs1.1 inputs2.1 inputs1.2 inputs2.2
        have y3Imaginary : star y3 = -y3 := by
          simpa only [y3, curve12_addY] using star_sumY x1 x2 y1 slope inputs1.1 inputs2.1 inputs1.2 slopeImaginary
        have denominator := twist_vertical_evaluation_nonzero evaluation evaluationCurve x3 y3 h3 y3Imaginary
        have numerator := twist_line_evaluation_nonzero evaluation evaluationCurve x1 y1 slope inputs1.1 inputs1.2 slopeImaginary
        have lineEq : normalizedLine (.some x1 y1 h1) (.some x2 y2 h2) = lineQuotient x1 y1 slope x3 := by
          change (if x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2 then _ else _) = _
          rw [if_neg vertical]
        refine ⟨_, div_ne_zero numerator denominator, ?_⟩
        rw [lineEq]
        exact lineQuotient_evaluates _ _ _ _ _ _ denominator

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.native_g1_x_real
#print axioms LeanCrypto.Proofs.BN254Tate.native_g1_y_real
#print axioms LeanCrypto.Proofs.BN254Tate.native_g1_y_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.real_imaginary_square_distinct
#print axioms LeanCrypto.Proofs.BN254Tate.twist_vertical_evaluation_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.twist_line_evaluation_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.normalizedLine_evaluates
