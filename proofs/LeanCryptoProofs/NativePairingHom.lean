import LeanCryptoProofs.NativeMillerFold
import LeanCryptoProofs.TateFinalGuards
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing

theorem miller_q_restrict (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (n : Nat) (point : twistQTorsion) :
    MillerAlgebra.miller (qReducedCocycle evaluation onCurve) n point =
      MillerAlgebra.miller (reducedCocycle evaluation onCurve) n point.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [MillerAlgebra.miller, ih]
    rfl

theorem pairingSecondHom_value (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (point : twistQTorsion) :
    ((pairingSecondHom evaluation onCurve point).toMul : BN254Fp12.Field) =
      millerValue evaluation onCurve LeanCrypto.BN254.G1.scalarPrime point.val := by
  change ((MillerAlgebra.miller (qReducedCocycle evaluation onCurve) _ point).toMul : BN254Fp12.Field) = _
  rw [miller_q_restrict]
  rfl

/-- The actual public native pairing constructs the value of the independently
derived second-argument homomorphism. Native success and a pairing equality
are conclusions, not hypotheses. -/
theorem pair_construct_second_hom (evaluation : LeanCrypto.BN254.G1.Affine) (point : Affine)
    (evaluationCurve : evaluation.onCurve = true) (pointCurve : point.onCurve = true)
    (torsion : LeanCrypto.BN254.G1.scalarPrime • BN254G2Group.affinePoint point pointCurve = 0) :
    ∃ result : Fp12, pair evaluation point = .ok result ∧
      BN254Fp12.model result =
        ((pairingSecondHom evaluation evaluationCurve (nativeTwistTorsion point pointCurve torsion)).toMul :
          BN254Fp12.Field) := by
  have groupTorsion : LeanCrypto.BN254.G1.scalarPrime • BN254G2Group.groupPoint (Jacobian.ofAffine point) = 0 := by
    rw [ofAffine_groupPoint point pointCurve]
    exact torsion
  have subgroup := (BN254G2Group.subgroup_check_iff _ (BN254G2Jacobian.ofAffine_admissible point pointCurve)).2 groupTorsion
  obtain ⟨value, constructed, valueMeaning⟩ := miller_value point pointCurve subgroup evaluation evaluationCurve
  refine ⟨value.pow finalExponent, ?_, ?_⟩
  · rw [pair_eq_candidate, pairCandidate_source]
    simp only [evaluationCurve, pointCurve, subgroup, Bool.not_true, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, constructed, bind, Except.bind, pure, Except.pure]
  · rw [BN254Fp12.model_pow, pairingSecondHom_value]
    exact valueMeaning

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.miller_q_restrict
#print axioms LeanCrypto.Proofs.BN254Tate.pairingSecondHom_value
#print axioms LeanCrypto.Proofs.BN254Tate.pair_construct_second_hom
