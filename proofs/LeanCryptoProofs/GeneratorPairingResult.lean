import LeanCryptoProofs.GeneratorHintedCertificate
import LeanCryptoProofs.GeneratorPowerCertificate
import LeanCryptoProofs.VerifierPairingEquation
import LeanCryptoProofs.TraceSourceComposition


noncomputable section
set_option autoImplicit false
set_option maxRecDepth 16384
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing Groth16Assembly
local instance : NeZero G1.scalarPrime := ⟨by decide⟩
local instance : Fact G1.scalarPrime.Prime := ⟨Primes.bn254_scalar_prime⟩

theorem generator_miller_value :
    miller (embedG2 G2.generator) (embedG1 G1.generator) = .ok generatorMillerFinal.fst := by
  have firstCurve : G1.generator.onCurve = true := by decide +kernel
  have secondCurve : G2.generator.onCurve = true := by decide +kernel
  have bits : Nat.log2 G1.scalarPrime + 1 = 254 := by decide +kernel
  have checked : hintedTraceCheck (embedG2 G2.generator) (embedG1 G1.generator)
      (Nat.log2 G1.scalarPrime + 1) 1 generatorMillerInitial generatorHintedRows = true := by
    rw [bits]
    exact generator_hinted_trace_checked
  have result := miller_from_hinted_trace (embedG2 G2.generator) (embedG1 G1.generator)
    (embedG2_onCurve _ secondCurve) (embedG1_onCurve _ firstCurve) generatorHintedRows generatorMillerInitial
    rfl (by decide +kernel) checked (by rfl)
  have final : traceLast generatorMillerInitial (generatorHintedRows.map Prod.snd) = generatorMillerFinal := rfl
  rw [final] at result
  exact result

#print axioms LeanCrypto.Proofs.BN254Tate.generator_miller_value

theorem generator_power_value : generatorMillerFinal.fst.pow finalExponent = generatorPowerFinal.accumulator := by
  have result := power_from_trace generatorPowerInitial generatorPowerStates rfl generator_power_trace_checked
  have final : traceLast generatorPowerInitial generatorPowerStates = generatorPowerFinal := rfl
  have base : generatorPowerInitial.base = generatorMillerFinal.fst := rfl
  have exponent : generatorPowerInitial.exponent = finalExponent := rfl
  rw [base, exponent, final] at result
  exact result

#print axioms LeanCrypto.Proofs.BN254Tate.generator_power_value

theorem generator_pair_value :
    pair G1.generator G2.generator = .ok generatorPowerFinal.accumulator := by
  have result := pair_from_miller G1.generator G2.generator (by decide +kernel) (by decide +kernel)
    BN254G2Order.generator_public_q_order generatorMillerFinal.fst generator_miller_value
  rw [generator_power_value] at result
  exact result

theorem generator_pair_nontrivial : pair G1.generator G2.generator ≠ .ok Fp12.one := by
  intro equal
  have values := Except.ok.inj (generator_pair_value.symm.trans equal)
  have checked := generator_power_nonunit
  rw [values] at checked
  contradiction

theorem g1_ofAffine_groupPoint (point : G1.Affine) (onCurve : point.onCurve = true) :
    BN254Group.groupPoint (G1.Jacobian.ofAffine point) = BN254Group.affinePoint point onCurve := by
  have finite : BN254Fp.model (G1.Jacobian.ofAffine point).z ≠ 0 := by simp [G1.Jacobian.ofAffine]
  have equation : BN254Jacobian.ProjectiveEquation (G1.Jacobian.ofAffine point) := by
    simpa [BN254Jacobian.ProjectiveEquation, G1.Jacobian.ofAffine] using (BN254Fp.affine_onCurve_iff point).1 onCurve
  simpa only [BN254Jacobian.normalized_ofAffine] using
    BN254Group.normalized_groupPoint (G1.Jacobian.ofAffine point) finite equation

theorem scalarPair_generator_nonzero : scalarPairHom (1 : Fr) 1 ≠ 0 := by
  have firstCurve : G1.generator.onCurve = true := by decide +kernel
  have secondCurve : G2.generator.onCurve = true := by decide +kernel
  have oneVal : (1 : Fr).val = 1 := by decide +kernel
  have firstSpan : BN254Group.affinePoint G1.generator firstCurve = scalarG1 1 := by
    change _ = (1 : Fr).val • BN254Group.groupPoint (G1.Jacobian.ofAffine G1.generator)
    rw [oneVal, one_nsmul, g1_ofAffine_groupPoint _ firstCurve]
  have secondSpan : BN254G2Group.affinePoint G2.generator secondCurve = scalarG2 1 := by
    change _ = (1 : Fr).val • BN254G2Group.groupPoint (G2.Jacobian.ofAffine G2.generator)
    rw [oneVal, one_nsmul, ofAffine_groupPoint _ secondCurve]
  obtain ⟨result, constructed, meaning⟩ := NativeVerifier.pair_scalar_construct G1.generator G2.generator
    firstCurve secondCurve 1 1 firstSpan secondSpan
  intro zero
  have modelOne : BN254Fp12.model result = BN254Fp12.model Fp12.one := by
    rw [meaning, zero, BN254Fp12.model_one]
    rfl
  have equal := BN254Fp12.model_injective modelOne
  rw [equal] at constructed
  exact generator_pair_nontrivial constructed

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.generator_pair_value
#print axioms LeanCrypto.Proofs.BN254Tate.generator_pair_nontrivial
#print axioms LeanCrypto.Proofs.BN254Tate.g1_ofAffine_groupPoint
#print axioms LeanCrypto.Proofs.BN254Tate.scalarPair_generator_nonzero
