import LeanCryptoProofs.ChordEvaluation

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

def nativeChordSlope (first second : LeanCrypto.BN254.G1.Affine) : BN254Fp12.Field :=
  chordSlope (BN254Fp12.model (embedG1 first).x) (BN254Fp12.model (embedG1 second).x)
    (BN254Fp12.model (embedG1 first).y) (BN254Fp12.model (embedG1 second).y)
def nativeChordIntercept (first second : LeanCrypto.BN254.G1.Affine) : BN254Fp12.Field :=
  chordIntercept (BN254Fp12.model (embedG1 first).x) (BN254Fp12.model (embedG1 second).x)
    (BN254Fp12.model (embedG1 first).y) (BN254Fp12.model (embedG1 second).y)

theorem nativeChord_notVertical (first second : LeanCrypto.BN254.G1.Affine)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y))) :
    ¬(BN254Fp12.model (embedG1 first).x = BN254Fp12.model (embedG1 second).x ∧
      BN254Fp12.model (embedG1 first).y =
        curve12.toAffine.negY (BN254Fp12.model (embedG1 second).x) (BN254Fp12.model (embedG1 second).y)) := by
  intro bad
  apply notVertical
  have x := bad.1
  have y := bad.2
  simp only [embedG1, model_embedFp] at x y
  refine ⟨fpHom.injective x, fpHom.injective ?_⟩
  simpa only [WeierstrassCurve.Affine.negY, curve12_coefficients, BN254Group.curve,
    zero_mul, sub_zero, map_neg] using y

theorem nativeChordAt_nonzero (first second : LeanCrypto.BN254.G1.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y)))
    (point : twistSubgroup) :
    chordAt (nativeChordSlope first second) (nativeChordIntercept first second) point.val ≠ 0 := by
  rcases point with ⟨point, twist⟩
  cases point with
  | zero => exact one_ne_zero
  | some x y h =>
    have firstEquation := native12_equation (embedG1 first) (embedG1_onCurve first firstCurve)
    have secondEquation := native12_equation (embedG1 second) (embedG1_onCurve second secondCurve)
    let roots := chordSection _ _ _ _ firstEquation secondEquation (nativeChord_notVertical first second notVertical)
    have root0 : roots.x0 = BN254Fp12.model (embedG1 first).x := rfl
    have root1 : roots.x1 = BN254Fp12.model (embedG1 second).x := rfl
    have root2 : roots.x2 = BN254Fp12.model (embedG1 (nativeChordThird first second)).x :=
      (nativeChordThird_x first second).symm
    have thirdCurve := nativeChordThird_onCurve first second firstCurve secondCurve notVertical
    have imaginary : star y = -y := twist.2
    apply section_line_nonzero _ _ roots x y
    · have eq := (WeierstrassCurve.Affine.equation_iff _ _).1 h.left
      simpa only [curve12_coefficients, zero_mul, add_zero] using eq
    · rw [root0, root1, root2]
      exact mul_ne_zero (mul_ne_zero
        (twist_vertical_evaluation_nonzero first firstCurve x y h imaginary)
        (twist_vertical_evaluation_nonzero second secondCurve x y h imaginary))
        (twist_vertical_evaluation_nonzero _ thirdCurve x y h imaginary)

theorem nativeChord_reduced_reciprocity (first second : LeanCrypto.BN254.G1.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y)))
    (q1 q2 : twistSubgroup) :
    reducedLine first firstCurve q1 q2 * reducedLine second secondCurve q1 q2 *
      reducedLine (nativeChordThird first second) (nativeChordThird_onCurve first second firstCurve secondCurve notVertical) q1 q2 =
      (chordAt (nativeChordSlope first second) (nativeChordIntercept first second) q1.val *
        chordAt (nativeChordSlope first second) (nativeChordIntercept first second) q2.val /
        chordAt (nativeChordSlope first second) (nativeChordIntercept first second) (q1.val + q2.val)) ^ finalExponent := by
  have firstEquation := native12_equation (embedG1 first) (embedG1_onCurve first firstCurve)
  have secondEquation := native12_equation (embedG1 second) (embedG1_onCurve second secondCurve)
  have notVertical12 := nativeChord_notVertical first second notVertical
  let roots := chordSection _ _ _ _ firstEquation secondEquation notVertical12
  have root0 : roots.x0 = BN254Fp12.model (embedG1 first).x := rfl
  have root1 : roots.x1 = BN254Fp12.model (embedG1 second).x := rfl
  have root2 : roots.x2 = BN254Fp12.model (embedG1 (nativeChordThird first second)).x :=
    (nativeChordThird_x first second).symm
  have thirdCurve := nativeChordThird_onCurve first second firstCurve secondCurve notVertical
  have separation (x y : BN254Fp12.Field) (h : curve12.toAffine.Nonsingular x y)
      (twist : IsTwistPoint (.some x y h)) : (roots.x0 - x) * (roots.x1 - x) * (roots.x2 - x) ≠ 0 := by
    have imaginary : star y = -y := twist.2
    rw [root0, root1, root2]
    exact mul_ne_zero (mul_ne_zero
      (twist_vertical_evaluation_nonzero first firstCurve x y h imaginary)
      (twist_vertical_evaluation_nonzero second secondCurve x y h imaginary))
      (twist_vertical_evaluation_nonzero _ thirdCurve x y h imaginary)
  have helper := section_explicit_reduced_product (nativeChordSlope first second)
    (nativeChordIntercept first second) roots separation q1 q2
  rw [root0, root1, root2] at helper
  have firstLine : nativeChordSlope first second * BN254Fp12.model (embedG1 first).x +
      nativeChordIntercept first second = BN254Fp12.model (embedG1 first).y := by
    unfold nativeChordSlope nativeChordIntercept chordIntercept
    ring
  have secondLine : nativeChordSlope first second * BN254Fp12.model (embedG1 second).x +
      nativeChordIntercept first second = BN254Fp12.model (embedG1 second).y :=
    (chord_second_on_line _ _ _ _ firstEquation secondEquation notVertical12).symm
  have thirdLine : nativeChordSlope first second * BN254Fp12.model (embedG1 (nativeChordThird first second)).x +
      nativeChordIntercept first second = BN254Fp12.model (embedG1 (nativeChordThird first second)).y := by
    rw [nativeChordThird_x, nativeChordThird_y]
    unfold nativeChordSlope nativeChordIntercept chordIntercept WeierstrassCurve.Affine.negAddY
    ring
  rw [firstLine, secondLine, thirdLine] at helper
  simpa only [reducedLine, evaluatedLine_explicit, ← mul_pow] using helper

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.nativeChord_notVertical
#print axioms LeanCrypto.Proofs.BN254Tate.nativeChordAt_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.nativeChord_reduced_reciprocity
