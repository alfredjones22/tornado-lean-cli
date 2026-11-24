import LeanCryptoProofs.GeneratorPairingResult
import LeanCryptoProofs.ScalarPairingFaithfulness
import LeanCryptoProofs.VerifierCompleteness

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.NativeVerifier
open LeanCrypto.BN254 LeanCrypto.Groth16 Groth16Assembly BN254Tate
local instance : NeZero G1.scalarPrime := ⟨by decide⟩
local instance : Fact G1.scalarPrime.Prime := ⟨Primes.bn254_scalar_prime⟩
local instance : Inhabited G1.Affine := ⟨G1.generator⟩

structure AffineProofSpans (proof : Verify.Proof) (triple : IdealGroth16.Triple Fr) : Prop where
  aCurve : proof.a.onCurve = true
  bCurve : proof.b.onCurve = true
  cCurve : proof.c.onCurve = true
  aSpan : BN254Group.affinePoint proof.a aCurve = scalarG1 triple.a
  bSpan : BN254G2Group.affinePoint proof.b bCurve = scalarG2 triple.b
  cSpan : BN254Group.affinePoint proof.c cCurve = scalarG1 triple.c

theorem actual_scalar_target_injective : Function.Injective scalarTargetHom :=
  scalarTargetHom_injective scalarPair_generator_nonzero

theorem verify_true_scalar_of_publicInput (key : Verify.VerifyingKey) (proof : Verify.Proof) (signals : Array Nat)
    (setup : IdealGroth16.Setup Fr) (icValues : Nat → Fr)
    (keyRelation : VerificationKeyRelation key setup icValues)
    (triple : IdealGroth16.Triple Fr) (proofSpans : AffineProofSpans proof triple)
    (vkX : G1.Affine) (inputCurve : vkX.onCurve = true)
    (publicInput : Verify.publicInputPoint key signals = .ok vkX)
    (inputSpan : BN254Group.affinePoint vkX inputCurve = scalarG1 setup.publicIC)
    (accepted : Verify.verify key proof signals = .ok true) :
    triple.a * triple.b = setup.alpha * setup.beta + setup.publicIC * setup.gamma + triple.c * setup.delta := by
  have negativeSpan : BN254Group.affinePoint (negativeNativeG1 proof.a)
      (negativeNativeG1_onCurve proof.a proofSpans.aCurve) = scalarG1 (-triple.a) := by
    rw [negative_affinePoint proof.a proofSpans.aCurve, proofSpans.aSpan, map_neg]
  obtain ⟨e0, call0, meaning0⟩ := pair_scalar_construct _ proof.b
    (negativeNativeG1_onCurve proof.a proofSpans.aCurve) proofSpans.bCurve
    (-triple.a) triple.b negativeSpan proofSpans.bSpan
  obtain ⟨e1, call1, meaning1⟩ := pair_scalar_construct _ _ keyRelation.alphaCurve keyRelation.betaCurve
    setup.alpha setup.beta keyRelation.alphaSpan keyRelation.betaSpan
  obtain ⟨e2, call2, meaning2⟩ := pair_scalar_construct _ _ inputCurve keyRelation.gammaCurve
    setup.publicIC setup.gamma inputSpan keyRelation.gammaSpan
  obtain ⟨e3, call3, meaning3⟩ := pair_scalar_construct _ _ proofSpans.cCurve keyRelation.deltaCurve
    triple.c setup.delta proofSpans.cSpan keyRelation.deltaSpan
  have source : Verify.verify key proof signals = .ok ((((e0.mul e1).mul e2).mul e3) == PairingField.Fp12.one) := by
    unfold Verify.verify
    rw [publicInput]
    change (do
      let v0 ← TatePairing.pair (negativeNativeG1 proof.a) proof.b
      let v1 ← TatePairing.pair key.alpha1 key.beta2
      let v2 ← TatePairing.pair vkX key.gamma2
      let v3 ← TatePairing.pair proof.c key.delta2
      return (((v0.mul v1).mul v2).mul v3) == PairingField.Fp12.one) = _
    rw [call0, call1, call2, call3]
    rfl
  have boolean := Except.ok.inj (source.symm.trans accepted)
  have modeled := (BN254Fp12.model_beq _ _).1 boolean
  simp only [BN254Fp12.model_mul, BN254Fp12.model_one, meaning0, meaning1, meaning2, meaning3] at modeled
  exact (scalar_pair_product_equation_iff scalarPair_generator_nonzero
    triple.a triple.b triple.c setup.alpha setup.beta setup.gamma setup.delta setup.publicIC).1 modeled

/-- Exact native verification equation on certified generator spans.
This is algebraic acceptance, not a cryptographic knowledge-soundness or
external Ethereum optimal-Ate implementation theorem. -/
theorem verify_scalar_iff (key : Verify.VerifyingKey) (proof : Verify.Proof) (signals : Array Nat)
    (setup : IdealGroth16.Setup Fr) (icValues : Nat → Fr)
    (keyRelation : VerificationKeyRelation key setup icValues)
    (counts : key.ic.size = signals.size + 1) (limit : signals.size ≤ Verify.maxPublicSignals)
    (canonical : signals.all (· < G1.scalarPrime) = true)
    (publicRelation : publicInputScalar icValues signals = setup.publicIC) (publicNonzero : setup.publicIC ≠ 0)
    (triple : IdealGroth16.Triple Fr) (proofSpans : AffineProofSpans proof triple) :
    Verify.verify key proof signals = .ok true ↔
      triple.a * triple.b = setup.alpha * setup.beta + setup.publicIC * setup.gamma + triple.c * setup.delta := by
  constructor
  · intro accepted
    have meaning := publicInputMeaning_scalar key signals icValues counts keyRelation.icSpan
    rw [publicRelation] at meaning
    have finite : publicInputMeaning key signals ≠ 0 := by
      rw [meaning]
      intro zero
      apply publicNonzero
      apply scalarG1_injective
      simpa only [map_zero] using zero
    obtain ⟨vkX, vkXCurve, constructed, span⟩ := publicInputPoint_construct key signals counts limit
      keyRelation.icCurves canonical finite
    rw [meaning] at span
    exact verify_true_scalar_of_publicInput key proof signals setup icValues keyRelation triple proofSpans
      vkX vkXCurve constructed span accepted
  · intro equation
    exact verify_construct key proof signals setup icValues keyRelation counts limit canonical publicRelation publicNonzero
      proofSpans.aCurve proofSpans.bCurve proofSpans.cCurve triple.a triple.b triple.c
      proofSpans.aSpan proofSpans.bSpan proofSpans.cSpan equation

end LeanCrypto.Proofs.NativeVerifier
#print axioms LeanCrypto.Proofs.NativeVerifier.actual_scalar_target_injective
#print axioms LeanCrypto.Proofs.NativeVerifier.verify_true_scalar_of_publicInput
#print axioms LeanCrypto.Proofs.NativeVerifier.verify_scalar_iff
