import LeanCryptoProofs.G1EvaluationModel
import LeanCryptoProofs.ChordSection

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

def nativeChordThird (first second : LeanCrypto.BN254.G1.Affine) : LeanCrypto.BN254.G1.Affine :=
  let x1 := BN254Fp.model first.x
  let x2 := BN254Fp.model second.x
  let y1 := BN254Fp.model first.y
  let y2 := BN254Fp.model second.y
  let slope := BN254Group.curve.toAffine.slope x1 x2 y1 y2
  nativeG1Affine (BN254Group.curve.toAffine.addX x1 x2 slope)
    (BN254Group.curve.toAffine.negAddY x1 x2 y1 slope)

theorem nativeChordThird_onCurve (first second : LeanCrypto.BN254.G1.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y))) :
    (nativeChordThird first second).onCurve = true := by
  apply nativeG1Affine_onCurve
  apply WeierstrassCurve.Affine.equation_negAdd _ _ notVertical
  · simpa [WeierstrassCurve.Affine.equation_iff, BN254Group.curve] using (BN254Fp.affine_onCurve_iff first).1 firstCurve
  · simpa [WeierstrassCurve.Affine.equation_iff, BN254Group.curve] using (BN254Fp.affine_onCurve_iff second).1 secondCurve

theorem nativeChordThird_x (first second : LeanCrypto.BN254.G1.Affine) :
    BN254Fp12.model (embedG1 (nativeChordThird first second)).x =
      curve12.toAffine.addX (BN254Fp12.model (embedG1 first).x) (BN254Fp12.model (embedG1 second).x)
        (chordSlope (BN254Fp12.model (embedG1 first).x) (BN254Fp12.model (embedG1 second).x)
          (BN254Fp12.model (embedG1 first).y) (BN254Fp12.model (embedG1 second).y)) := by
  change BN254Fp12.model (embedFp _) = curve12.toAffine.addX (BN254Fp12.model (embedFp first.x))
    (BN254Fp12.model (embedFp second.x)) (chordSlope _ _ (BN254Fp12.model (embedFp first.y)) (BN254Fp12.model (embedFp second.y)))
  simp only [embedG1, model_embedFp, nativeChordThird, nativeG1Affine, BN254Fp.model_encode, chordSlope]
  have slope : curve12.toAffine.slope (fpHom (BN254Fp.model first.x)) (fpHom (BN254Fp.model second.x))
      (fpHom (BN254Fp.model first.y)) (fpHom (BN254Fp.model second.y)) =
      fpHom (BN254Group.curve.toAffine.slope (BN254Fp.model first.x) (BN254Fp.model second.x)
        (BN254Fp.model first.y) (BN254Fp.model second.y)) :=
    WeierstrassCurve.Affine.map_slope (W := BN254Group.curve.toAffine) fpHom _ _ _ _
  rw [slope]
  exact (WeierstrassCurve.Affine.map_addX (W' := BN254Group.curve.toAffine) fpHom _ _ _).symm

theorem nativeChordThird_y (first second : LeanCrypto.BN254.G1.Affine) :
    BN254Fp12.model (embedG1 (nativeChordThird first second)).y =
      curve12.toAffine.negAddY (BN254Fp12.model (embedG1 first).x) (BN254Fp12.model (embedG1 second).x)
        (BN254Fp12.model (embedG1 first).y)
        (chordSlope (BN254Fp12.model (embedG1 first).x) (BN254Fp12.model (embedG1 second).x)
          (BN254Fp12.model (embedG1 first).y) (BN254Fp12.model (embedG1 second).y)) := by
  change BN254Fp12.model (embedFp _) = curve12.toAffine.negAddY (BN254Fp12.model (embedFp first.x))
    (BN254Fp12.model (embedFp second.x)) (BN254Fp12.model (embedFp first.y))
    (chordSlope _ _ (BN254Fp12.model (embedFp first.y)) (BN254Fp12.model (embedFp second.y)))
  simp only [embedG1, model_embedFp, nativeChordThird, nativeG1Affine, BN254Fp.model_encode, chordSlope]
  have slope : curve12.toAffine.slope (fpHom (BN254Fp.model first.x)) (fpHom (BN254Fp.model second.x))
      (fpHom (BN254Fp.model first.y)) (fpHom (BN254Fp.model second.y)) =
      fpHom (BN254Group.curve.toAffine.slope (BN254Fp.model first.x) (BN254Fp.model second.x)
        (BN254Fp.model first.y) (BN254Fp.model second.y)) :=
    WeierstrassCurve.Affine.map_slope (W := BN254Group.curve.toAffine) fpHom _ _ _ _
  rw [slope]
  exact (WeierstrassCurve.Affine.map_negAddY (W' := BN254Group.curve.toAffine) fpHom _ _ _ _).symm

theorem chord_second_on_line (x1 x2 y1 y2 : BN254Fp12.Field)
    (h1 : curve12.toAffine.Equation x1 y1) (h2 : curve12.toAffine.Equation x2 y2)
    (notVertical : ¬(x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2)) :
    y2 = chordSlope x1 x2 y1 y2 * x2 + chordIntercept x1 x2 y1 y2 := by
  by_cases same : x1 = x2
  · have sameY := WeierstrassCurve.Affine.Y_eq_of_Y_ne h1 h2 same (fun h => notVertical ⟨same, h⟩)
    rw [← same, ← sameY]
    unfold chordIntercept
    ring
  · unfold chordIntercept chordSlope
    rw [WeierstrassCurve.Affine.slope_of_X_ne same]
    field_simp [sub_ne_zero.mpr same]
    ring

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.nativeChordThird_onCurve
#print axioms LeanCrypto.Proofs.BN254Tate.nativeChordThird_x
#print axioms LeanCrypto.Proofs.BN254Tate.nativeChordThird_y
#print axioms LeanCrypto.Proofs.BN254Tate.chord_second_on_line
