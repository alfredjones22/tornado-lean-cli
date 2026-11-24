import LeanCryptoProofs.VerifierInputConstruction
import LeanCryptoProofs.VerifierPairingEquation
import LeanCryptoProofs.AssemblyVerifierInputs

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.NativeVerifier
open LeanCrypto.BN254 LeanCrypto.Groth16 Groth16Assembly
local instance : NeZero G1.scalarPrime := ⟨by decide⟩
local instance : Fact G1.scalarPrime.Prime := ⟨Primes.bn254_scalar_prime⟩
local instance : Inhabited G1.Affine := ⟨G1.generator⟩

def publicInputScalar (values : Nat → Fr) (signals : Array Nat) : Fr :=
  values 0 + ((List.range' 0 signals.size).map (fun index => ((signals[index]! : Nat) : Fr) * values (index + 1))).sum

structure VerificationKeyRelation (key : Verify.VerifyingKey) (setup : IdealGroth16.Setup Fr)
    (icValues : Nat → Fr) : Prop where
  alphaCurve : key.alpha1.onCurve = true
  betaCurve : key.beta2.onCurve = true
  gammaCurve : key.gamma2.onCurve = true
  deltaCurve : key.delta2.onCurve = true
  icCurves : key.ic.all (·.onCurve) = true
  alphaSpan : BN254Group.affinePoint key.alpha1 alphaCurve = scalarG1 setup.alpha
  betaSpan : BN254G2Group.affinePoint key.beta2 betaCurve = scalarG2 setup.beta
  gammaSpan : BN254G2Group.affinePoint key.gamma2 gammaCurve = scalarG2 setup.gamma
  deltaSpan : BN254G2Group.affinePoint key.delta2 deltaCurve = scalarG2 setup.delta
  icSpan : ∀ index, index < key.ic.size →
    BN254Group.groupPoint (G1.Jacobian.ofAffine key.ic[index]!) = scalarG1 (icValues index)

theorem publicInputMeaning_scalar (key : Verify.VerifyingKey) (signals : Array Nat) (values : Nat → Fr)
    (counts : key.ic.size = signals.size + 1)
    (span : ∀ index, index < key.ic.size →
      BN254Group.groupPoint (G1.Jacobian.ofAffine key.ic[index]!) = scalarG1 (values index)) :
    publicInputMeaning key signals = scalarG1 (publicInputScalar values signals) := by
  have sumMeaning (indices : List Nat) (bounds : ∀ index ∈ indices, index + 1 < key.ic.size) :
      (indices.map (inputContribution key signals)).sum =
        scalarG1 ((indices.map (fun index => ((signals[index]! : Nat) : Fr) * values (index + 1))).sum) := by
    induction indices with
    | nil => simp only [List.map_nil, List.sum_nil, map_zero]
    | cons index indices ih =>
      simp only [List.map_cons, List.sum_cons, map_add]
      rw [ih (fun j member => bounds j (by simp [member]))]
      congr 1
      unfold inputContribution
      rw [span (index + 1) (bounds index (by simp)), scalarG1_mul_nat]
  unfold publicInputMeaning publicInputScalar
  rw [span 0 (by omega), map_add]
  congr 1
  exact sumMeaning _ (fun index member => by obtain ⟨offset, bound, equal⟩ := List.mem_range'.mp member; omega)

/-- Actual native verifier completeness from an independently specified key
relation and scalar equation. Every native public-input/pairing call is
constructed; no successful verifier/public-input check is assumed. -/
theorem verify_construct (key : Verify.VerifyingKey) (proof : Verify.Proof) (signals : Array Nat)
    (setup : IdealGroth16.Setup Fr) (icValues : Nat → Fr)
    (keyRelation : VerificationKeyRelation key setup icValues)
    (counts : key.ic.size = signals.size + 1) (limit : signals.size ≤ Verify.maxPublicSignals)
    (canonical : signals.all (· < G1.scalarPrime) = true)
    (publicRelation : publicInputScalar icValues signals = setup.publicIC) (publicNonzero : setup.publicIC ≠ 0)
    (aCurve : proof.a.onCurve = true) (bCurve : proof.b.onCurve = true) (cCurve : proof.c.onCurve = true)
    (a b c : Fr)
    (aSpan : BN254Group.affinePoint proof.a aCurve = scalarG1 a)
    (bSpan : BN254G2Group.affinePoint proof.b bCurve = scalarG2 b)
    (cSpan : BN254Group.affinePoint proof.c cCurve = scalarG1 c)
    (equation : a * b = setup.alpha * setup.beta + setup.publicIC * setup.gamma + c * setup.delta) :
    Verify.verify key proof signals = .ok true := by
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
  exact verify_construct_of_publicInput key proof signals vkX vkXCurve constructed aCurve bCurve cCurve
    keyRelation.alphaCurve keyRelation.betaCurve keyRelation.gammaCurve keyRelation.deltaCurve
    a b c setup.alpha setup.beta setup.gamma setup.delta setup.publicIC
    aSpan bSpan cSpan keyRelation.alphaSpan keyRelation.betaSpan keyRelation.gammaSpan keyRelation.deltaSpan span equation

/-- Honest setup/QAP compatibility for the actual original assembly yields
the actual native verifier's accepting result, on its explicit finite-output
domain. The normalized proof points come from the original assembly. -/
theorem assembly_qap_verifies (queryKey : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (r s : Nat)
    (valid : ValidKey queryKey) (dimensions : Dimensions queryKey witness h)
    (canonical : Canonical witness h r s) (span : KeySpan queryKey values)
    (setup : IdealGroth16.Setup Fr) (a b c : Polynomial Fr) (tau : Fr) (domain : Nat)
    (qapRelation : QapRelation queryKey values witness h setup a b c tau domain)
    (qap : a.eval tau * b.eval tau - c.eval tau =
      (LeanCrypto.Proofs.FFT.coeffPolynomial h).eval tau * (tau ^ domain - 1))
    (verificationKey : Verify.VerifyingKey) (icValues : Nat → Fr)
    (verificationRelation : VerificationKeyRelation verificationKey setup icValues)
    (counts : verificationKey.ic.size = (witness.extract 1 (queryKey.nPublic + 1)).size + 1)
    (limit : (witness.extract 1 (queryKey.nPublic + 1)).size ≤ Verify.maxPublicSignals)
    (publicRelation : publicInputScalar icValues (witness.extract 1 (queryKey.nPublic + 1)) = setup.publicIC)
    (publicNonzero : setup.publicIC ≠ 0)
    (aNonzero : (scalarOutput queryKey values witness h r s).a ≠ 0)
    (bNonzero : (scalarOutput queryKey values witness h r s).b ≠ 0)
    (cNonzero : (scalarOutput queryKey values witness h r s).c ≠ 0) :
    ∃ normalized : NormalizedAssembly (construction queryKey witness h r s) (scalarOutput queryKey values witness h r s),
      Verify.verify verificationKey normalized.proof (witness.extract 1 (queryKey.nPublic + 1)) = .ok true := by
  obtain ⟨normalized⟩ := construction_normalized queryKey values witness h r s valid dimensions canonical span
    aNonzero bNonzero cNonzero
  refine ⟨normalized, ?_⟩
  exact verify_construct verificationKey normalized.proof _ setup icValues verificationRelation counts limit
    (extract_canonical witness canonical.witness _ _) publicRelation publicNonzero
    normalized.aCurve normalized.bCurve normalized.cCurve _ _ _ normalized.aSpan normalized.bSpan normalized.cSpan
    (scalarOutput_verifier_equation queryKey values witness h setup a b c tau domain qapRelation qap r s)

end LeanCrypto.Proofs.NativeVerifier
#print axioms LeanCrypto.Proofs.NativeVerifier.publicInputMeaning_scalar
#print axioms LeanCrypto.Proofs.NativeVerifier.verify_construct
#print axioms LeanCrypto.Proofs.NativeVerifier.assembly_qap_verifies
