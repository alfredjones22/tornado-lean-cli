import LeanCryptoProofs.MillerInputConstruction
import LeanCryptoProofs.TateFinalGuards
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing
open BN254G2Group BN254G2Jacobian

/-- Universal constructive completeness of the actual native pairing's
arithmetic and shape guards. The independent q-torsion condition is on the
input group point. Bilinearity/equivalence to divisor-defined Tate pairing
is a separate mathematical theorem. -/
theorem pair_construct (g1 : LeanCrypto.BN254.G1.Affine) (g2 : Affine)
    (g1Curve : g1.onCurve = true) (g2Curve : g2.onCurve = true)
    (torsion : LeanCrypto.BN254.G1.scalarPrime • groupPoint (Jacobian.ofAffine g2) = 0) :
    ∃ result : Fp12,
      pair g1 g2 = .ok result ∧ BN254Fp12.model result ≠ 0 ∧
      BN254Fp12.model result ^ LeanCrypto.BN254.G1.scalarPrime = 1 := by
  have subgroup := (subgroup_check_iff _ (ofAffine_admissible g2 g2Curve)).2 torsion
  obtain ⟨value, constructed⟩ := miller_construct g2 g2Curve subgroup g1 g1Curve
  refine ⟨value.pow finalExponent, ?_, final_power_nonzero value (miller_success_nonzero _ _ _ constructed), ?_⟩
  · rw [pair_eq_candidate, pairCandidate_source]
    simp only [g1Curve, g2Curve, subgroup, Bool.not_true, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte, constructed, bind, Except.bind, pure, Except.pure]
  · have order := (BN254Fp12.model_beq _ _).1
      (final_power_order value (miller_success_nonzero _ _ _ constructed))
    simpa only [BN254Fp12.model_pow, BN254Fp12.model_one] using order

theorem generator_pair_construct (g1 : LeanCrypto.BN254.G1.Affine)
    (g1Curve : g1.onCurve = true) :
    ∃ result : Fp12, pair g1 generator = .ok result := by
  obtain ⟨result, constructed, _, _⟩ := pair_construct g1 generator g1Curve
    (by decide +kernel) generator_q_annihilates
  exact ⟨result, constructed⟩

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.pair_construct
#print axioms LeanCrypto.Proofs.BN254Tate.generator_pair_construct
