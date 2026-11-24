import LeanCryptoProofs.NativePairingHom

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

def nativeG1Affine (x y : BN254Group.Field) : LeanCrypto.BN254.G1.Affine :=
  ⟨BN254Fp.encode x, BN254Fp.encode y⟩

theorem nativeG1Affine_onCurve (x y : BN254Group.Field)
    (equation : BN254Group.curve.toAffine.Equation x y) : (nativeG1Affine x y).onCurve = true := by
  apply (BN254Fp.affine_onCurve_iff _).2
  simp only [nativeG1Affine, BN254Fp.model_encode]
  simpa [WeierstrassCurve.Affine.equation_iff, BN254Group.curve] using equation

def firstEmbedding : BN254Group.curve.toAffine.Point → curve12.toAffine.Point
  | .zero => 0
  | .some x y h => modelPoint (embedG1 (nativeG1Affine x y))
      (embedG1_onCurve _ (nativeG1Affine_onCurve x y h.left))

theorem firstEmbedding_some (x y : BN254Group.Field) (h : BN254Group.curve.toAffine.Nonsingular x y) :
    firstEmbedding (.some x y h) = .some (fpHom x) (fpHom y)
      ((WeierstrassCurve.Affine.map_nonsingular (W := BN254Group.curve.toAffine) (f := fpHom) x y fpHom.injective).2 h) := by
  simp only [firstEmbedding, modelPoint, nativeG1Affine, embedG1, model_embedFp, BN254Fp.model_encode]

theorem firstEmbedding_add (first second : BN254Group.curve.toAffine.Point) :
    firstEmbedding (first + second) = firstEmbedding first + firstEmbedding second := by
  cases first with
  | zero => rfl
  | some x1 y1 h1 =>
    cases second with
    | zero => rfl
    | some x2 y2 h2 =>
      rw [firstEmbedding_some, firstEmbedding_some]
      by_cases vertical : x1 = x2 ∧ y1 = BN254Group.curve.toAffine.negY x2 y2
      · have mappedVertical : fpHom x1 = fpHom x2 ∧ fpHom y1 = curve12.toAffine.negY (fpHom x2) (fpHom y2) := by
          simpa only [WeierstrassCurve.Affine.negY, BN254Group.curve, curve12_coefficients,
            zero_mul, sub_zero, map_neg] using And.intro (congrArg fpHom vertical.1) (congrArg fpHom vertical.2)
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq vertical.1 vertical.2,
          WeierstrassCurve.Affine.Point.add_of_Y_eq mappedVertical.1 mappedVertical.2]
        rfl
      · have mappedNotVertical : ¬(fpHom x1 = fpHom x2 ∧
            fpHom y1 = curve12.toAffine.negY (fpHom x2) (fpHom y2)) := by
          intro bad
          apply vertical
          refine ⟨fpHom.injective bad.1, fpHom.injective ?_⟩
          simpa only [WeierstrassCurve.Affine.negY, BN254Group.curve, curve12_coefficients,
            zero_mul, sub_zero, map_neg] using bad.2
        rw [WeierstrassCurve.Affine.Point.add_some vertical,
          WeierstrassCurve.Affine.Point.add_some mappedNotVertical, firstEmbedding_some]
        have slope : fpHom (BN254Group.curve.toAffine.slope x1 x2 y1 y2) =
            curve12.toAffine.slope (fpHom x1) (fpHom x2) (fpHom y1) (fpHom y2) := by
          exact (WeierstrassCurve.Affine.map_slope (W := BN254Group.curve.toAffine) fpHom x1 x2 y1 y2).symm
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        rw [← slope]
        exact ⟨(WeierstrassCurve.Affine.map_addX (W' := BN254Group.curve.toAffine)
          fpHom x1 x2 _).symm, (WeierstrassCurve.Affine.map_addY (W' := BN254Group.curve.toAffine)
          fpHom x1 y1 x2 _).symm⟩

def firstEmbeddingHom : BN254Group.curve.toAffine.Point →+ curve12.toAffine.Point where
  toFun := firstEmbedding
  map_zero' := rfl
  map_add' := firstEmbedding_add

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.nativeG1Affine_onCurve
#print axioms LeanCrypto.Proofs.BN254Tate.firstEmbedding_some
#print axioms LeanCrypto.Proofs.BN254Tate.firstEmbedding_add
