import LeanCryptoProofs.NativeChordReciprocity
import LeanCryptoProofs.FirstArgumentNegation

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing
attribute [local irreducible] MillerAlgebra.miller

def chordPhi (first second : LeanCrypto.BN254.G1.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y)))
    (point : twistSubgroup) : Additive BN254Fp12.Fieldˣ :=
  Additive.ofMul (Units.mk0
    (chordAt (nativeChordSlope first second) (nativeChordIntercept first second) point.val ^ finalExponent)
    (pow_ne_zero _ (nativeChordAt_nonzero first second firstCurve secondCurve notVertical point)))

theorem chordPhi_zero (first second : LeanCrypto.BN254.G1.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y))) :
    chordPhi first second firstCurve secondCurve notVertical 0 = 0 := by
  apply Units.val_injective
  exact one_pow _

theorem chordPhi_q_order (first second : LeanCrypto.BN254.G1.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y)))
    (point : twistSubgroup) :
    LeanCrypto.BN254.G1.scalarPrime • chordPhi first second firstCurve secondCurve notVertical point = 0 := by
  change (chordPhi first second firstCurve secondCurve notVertical point).toMul ^ LeanCrypto.BN254.G1.scalarPrime = 1
  apply Units.val_injective
  change (_ ^ finalExponent) ^ LeanCrypto.BN254.G1.scalarPrime = 1
  rw [← pow_mul, final_exponent_product]
  exact BN254Fp12.field_fermat _ (nativeChordAt_nonzero first second firstCurve secondCurve notVertical point)

theorem chord_cocycle_coboundary (first second : LeanCrypto.BN254.G1.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y)))
    (q1 q2 : twistSubgroup) :
    (reducedCocycle first firstCurve).value q1 q2 + (reducedCocycle second secondCurve).value q1 q2 +
      (reducedCocycle (nativeChordThird first second)
        (nativeChordThird_onCurve first second firstCurve secondCurve notVertical)).value q1 q2 =
      chordPhi first second firstCurve secondCurve notVertical q1 +
        chordPhi first second firstCurve secondCurve notVertical q2 -
        chordPhi first second firstCurve secondCurve notVertical (q1 + q2) := by
  apply Units.val_injective
  change reducedLine first firstCurve q1 q2 * reducedLine second secondCurve q1 q2 *
    reducedLine (nativeChordThird first second) _ q1 q2 = (_ ^ finalExponent) * (_ ^ finalExponent) / (_ ^ finalExponent)
  rw [nativeChord_reduced_reciprocity first second firstCurve secondCurve notVertical q1 q2, div_pow, mul_pow]
  rfl

theorem millerValue_chord (first second : LeanCrypto.BN254.G1.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (notVertical : ¬(BN254Fp.model first.x = BN254Fp.model second.x ∧
      BN254Fp.model first.y = BN254Group.curve.toAffine.negY (BN254Fp.model second.x) (BN254Fp.model second.y)))
    (point : twistSubgroup) (torsion : LeanCrypto.BN254.G1.scalarPrime • point = 0) :
    millerValue first firstCurve LeanCrypto.BN254.G1.scalarPrime point *
      millerValue second secondCurve LeanCrypto.BN254.G1.scalarPrime point *
      millerValue (nativeChordThird first second)
        (nativeChordThird_onCurve first second firstCurve secondCurve notVertical) LeanCrypto.BN254.G1.scalarPrime point = 1 := by
  have telescope := MillerAlgebra.miller_three_coboundary_q
    (reducedCocycle first firstCurve) (reducedCocycle second secondCurve)
    (reducedCocycle (nativeChordThird first second) (nativeChordThird_onCurve first second firstCurve secondCurve notVertical))
    (chordPhi first second firstCurve secondCurve notVertical)
    (chordPhi_zero first second firstCurve secondCurve notVertical)
    (chord_cocycle_coboundary first second firstCurve secondCurve notVertical)
    LeanCrypto.BN254.G1.scalarPrime point torsion
    (chordPhi_q_order first second firstCurve secondCurve notVertical point)
  exact congrArg (fun value : Additive BN254Fp12.Fieldˣ => (value.toMul : BN254Fp12.Field)) telescope

theorem millerValue_negative (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (n : Nat) (point : twistSubgroup) :
    millerValue evaluation onCurve n point *
      millerValue (negativeNativeG1 evaluation) (negativeNativeG1_onCurve evaluation onCurve) n point = 1 := by
  induction n with
  | zero => simp [millerValue, MillerAlgebra.miller]
  | succ n ih =>
    rw [millerValue_succ, millerValue_succ]
    calc
      _ = (millerValue evaluation onCurve n point * millerValue (negativeNativeG1 evaluation)
          (negativeNativeG1_onCurve evaluation onCurve) n point) *
          (reducedLine evaluation onCurve (n • point) point *
            reducedLine (negativeNativeG1 evaluation) (negativeNativeG1_onCurve evaluation onCurve) (n • point) point) := by ring
      _ = 1 := by rw [ih, reducedLine_negative, mul_one]

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.chordPhi_zero
#print axioms LeanCrypto.Proofs.BN254Tate.chordPhi_q_order
#print axioms LeanCrypto.Proofs.BN254Tate.chord_cocycle_coboundary
#print axioms LeanCrypto.Proofs.BN254Tate.millerValue_chord
#print axioms LeanCrypto.Proofs.BN254Tate.millerValue_negative
