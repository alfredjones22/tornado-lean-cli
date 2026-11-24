import LeanCryptoProofs.G2Embedding
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 LeanCrypto.BN254.TatePairing LeanCrypto.BN254.PairingField

def millerValue (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (n : Nat) (point : twistSubgroup) : BN254Fp12.Field :=
  ((MillerAlgebra.miller (reducedCocycle evaluation onCurve) n point).toMul : BN254Fp12.Field)

theorem millerValue_one (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (point : twistSubgroup) : millerValue evaluation onCurve 1 point = 1 := by
  change (1 : BN254Fp12.Field) * reducedLine evaluation onCurve (0 • point) point = 1
  rw [zero_nsmul, reducedLine_zero_left, mul_one]

theorem millerValue_double (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (n : Nat) (point : twistSubgroup) :
    millerValue evaluation onCurve (2 * n) point =
      millerValue evaluation onCurve n point ^ 2 * reducedLine evaluation onCurve (n • point) (n • point) := by
  unfold millerValue
  rw [two_mul, MillerAlgebra.miller_nat_add]
  change (_ * _) * _ = _ ^ 2 * _
  rw [pow_two]
  rfl

theorem millerValue_succ (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (n : Nat) (point : twistSubgroup) :
    millerValue evaluation onCurve (n + 1) point =
      millerValue evaluation onCurve n point * reducedLine evaluation onCurve (n • point) point := rfl

theorem native_line_reduced (first second : Affine) (firstCurve : first.onCurve = true)
    (secondCurve : second.onCurve = true)
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true)
    (factor : Fp12) (sum : Option Point)
    (actual : nativeLineAndSum (embedG2 first) (embedG2 second) (embedG1 evaluation) = .ok (factor, sum)) :
    BN254Fp12.model factor ^ finalExponent =
      reducedLine evaluation evaluationCurve (embedTwistHom (BN254G2Group.affinePoint first firstCurve))
        (embedTwistHom (BN254G2Group.affinePoint second secondCurve)) := by
  obtain ⟨value, result, constructed, _, evaluated⟩ := nativeLine_graph (embedG2 first) (embedG2 second)
    (embedG2_onCurve first firstCurve) (embedG2_onCurve second secondCurve)
    (native_embed_twist first firstCurve) (native_embed_twist second secondCurve) evaluation evaluationCurve
  have equal := congrArg Prod.fst (Except.ok.inj (actual.symm.trans constructed))
  change factor = value at equal
  rw [← equal] at evaluated
  have chosen := evaluatedLine_evaluates evaluation evaluationCurve
    (embedTwistHom (BN254G2Group.affinePoint first firstCurve))
    (embedTwistHom (BN254G2Group.affinePoint second secondCurve))
  have firstPoint : (embedTwistHom (BN254G2Group.affinePoint first firstCurve)).val =
      modelPoint (embedG2 first) (embedG2_onCurve first firstCurve) := embedGroup_native first firstCurve
  have secondPoint : (embedTwistHom (BN254G2Group.affinePoint second secondCurve)).val =
      modelPoint (embedG2 second) (embedG2_onCurve second secondCurve) := embedGroup_native second secondCurve
  rw [firstPoint, secondPoint] at chosen
  exact congrArg (fun value : BN254Fp12.Field => value ^ finalExponent)
    (evaluates_unique _ _ _ _ _ evaluated chosen)

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.millerValue_one
#print axioms LeanCrypto.Proofs.BN254Tate.millerValue_double
#print axioms LeanCrypto.Proofs.BN254Tate.millerValue_succ
#print axioms LeanCrypto.Proofs.BN254Tate.native_line_reduced
