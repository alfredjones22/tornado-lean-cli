import LeanCryptoProofs.FirstMillerIdentities
import LeanCryptoProofs.NormalizationGroupLaw

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing
attribute [local irreducible] MillerAlgebra.miller

theorem millerValue_native_sum (first second : LeanCrypto.BN254.G1.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y)))
    (point : twistSubgroup) (torsion : LeanCrypto.BN254.G1.scalarPrime • point = 0) :
    millerValue (negativeNativeG1 (nativeChordThird first second))
      (negativeNativeG1_onCurve _ (nativeChordThird_onCurve first second firstCurve secondCurve notVertical))
      LeanCrypto.BN254.G1.scalarPrime point =
    millerValue first firstCurve LeanCrypto.BN254.G1.scalarPrime point *
      millerValue second secondCurve LeanCrypto.BN254.G1.scalarPrime point := by
  have triple := millerValue_chord first second firstCurve secondCurve notVertical point torsion
  have negative := millerValue_negative (nativeChordThird first second)
    (nativeChordThird_onCurve first second firstCurve secondCurve notVertical) LeanCrypto.BN254.G1.scalarPrime point
  calc
    _ = (millerValue first firstCurve LeanCrypto.BN254.G1.scalarPrime point *
          millerValue second secondCurve LeanCrypto.BN254.G1.scalarPrime point *
          millerValue (nativeChordThird first second) _ LeanCrypto.BN254.G1.scalarPrime point) *
          millerValue (negativeNativeG1 (nativeChordThird first second)) _ LeanCrypto.BN254.G1.scalarPrime point := by rw [triple, one_mul]
    _ = _ := by rw [mul_assoc, negative, mul_one]

theorem nativeG1Affine_negative (x y : BN254Group.Field) :
    nativeG1Affine x (BN254Group.curve.toAffine.negY x y) = negativeNativeG1 (nativeG1Affine x y) := by
  have equal : BN254Fp.encode (BN254Group.curve.toAffine.negY x y) = (BN254Fp.encode y).neg := by
    apply BN254Fp.model_injective
    simp only [BN254Fp.model_encode, BN254Fp.model_neg]
    simp only [WeierstrassCurve.Affine.negY, BN254Group.curve, zero_mul, sub_zero]
  exact congrArg (fun value => LeanCrypto.BN254.G1.Affine.mk (BN254Fp.encode x) value) equal

theorem nativeG1Affine_sum (x1 x2 y1 y2 : BN254Group.Field) :
    nativeG1Affine (BN254Group.curve.toAffine.addX x1 x2 (BN254Group.curve.toAffine.slope x1 x2 y1 y2))
      (BN254Group.curve.toAffine.addY x1 x2 y1 (BN254Group.curve.toAffine.slope x1 x2 y1 y2)) =
      negativeNativeG1 (nativeChordThird (nativeG1Affine x1 y1) (nativeG1Affine x2 y2)) := by
  simp only [nativeChordThird, nativeG1Affine, BN254Fp.model_encode]
  exact nativeG1Affine_negative _ _

def firstValue (evaluation : BN254Group.curve.toAffine.Point) (point : twistQTorsion) : Additive BN254Fp12.Fieldˣ :=
  match evaluation with
  | .zero => 0
  | .some x y h => pairingSecondHom (nativeG1Affine x y) (nativeG1Affine_onCurve x y h.left) point

theorem firstValue_add (first second : BN254Group.curve.toAffine.Point) (point : twistQTorsion) :
    firstValue (first + second) point = firstValue first point + firstValue second point := by
  cases first with
  | zero => exact (zero_add _).symm
  | some x1 y1 h1 =>
    cases second with
    | zero => exact (add_zero _).symm
    | some x2 y2 h2 =>
      let a := nativeG1Affine x1 y1
      let b := nativeG1Affine x2 y2
      have aCurve : a.onCurve = true := nativeG1Affine_onCurve x1 y1 h1.left
      have bCurve : b.onCurve = true := nativeG1Affine_onCurve x2 y2 h2.left
      by_cases vertical : x1 = x2 ∧ y1 = BN254Group.curve.toAffine.negY x2 y2
      · have bNegative : b = negativeNativeG1 a := by
          dsimp only [a, b]
          rw [← nativeG1Affine_negative]
          have y2eq : y2 = BN254Group.curve.toAffine.negY x1 y1 := by
            rw [vertical.1, vertical.2, WeierstrassCurve.Affine.negY_negY]
          rw [vertical.1, y2eq, vertical.1]
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq vertical.1 vertical.2]
        apply Units.val_injective
        change (1 : BN254Fp12.Field) =
          ((pairingSecondHom a aCurve point).toMul : BN254Fp12.Field) *
          ((pairingSecondHom b bCurve point).toMul : BN254Fp12.Field)
        rw [pairingSecondHom_value, pairingSecondHom_value]
        have inverse := (millerValue_negative a aCurve LeanCrypto.BN254.G1.scalarPrime point.val).symm
        simpa only [bNegative] using inverse
      · have nativeNotVertical : ¬(BN254Fp.model a.x = BN254Fp.model b.x ∧
            BN254Fp.model a.y = BN254Group.curve.toAffine.negY (BN254Fp.model b.x) (BN254Fp.model b.y)) := by
          simpa only [a, b, nativeG1Affine, BN254Fp.model_encode] using vertical
        rw [WeierstrassCurve.Affine.Point.add_some vertical]
        apply Units.val_injective
        change ((pairingSecondHom (nativeG1Affine _ _) _ point).toMul : BN254Fp12.Field) =
          ((pairingSecondHom a aCurve point).toMul : BN254Fp12.Field) *
          ((pairingSecondHom b bCurve point).toMul : BN254Fp12.Field)
        rw [pairingSecondHom_value, pairingSecondHom_value, pairingSecondHom_value]
        have sum := millerValue_native_sum a b aCurve bCurve nativeNotVertical point.val point.property
        simpa only [a, b, ← nativeG1Affine_sum] using sum

def firstPairingHom (point : twistQTorsion) : BN254Group.curve.toAffine.Point →+ Additive BN254Fp12.Fieldˣ where
  toFun evaluation := firstValue evaluation point
  map_zero' := rfl
  map_add' first second := firstValue_add first second point

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.millerValue_native_sum
#print axioms LeanCrypto.Proofs.BN254Tate.nativeG1Affine_negative
#print axioms LeanCrypto.Proofs.BN254Tate.nativeG1Affine_sum
#print axioms LeanCrypto.Proofs.BN254Tate.firstValue_add
