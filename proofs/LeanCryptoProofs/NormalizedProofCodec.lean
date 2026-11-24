import LeanCryptoProofs.JacobianNormalization
import LeanCryptoProofs.ProofCodec

/-! The actual serializer is constructed from independently admitted finite
G1 A/C points and an explicitly supplied normalized G2 output. No claim of
G2 normalization completeness, MSM/group semantics, or Groth16 correctness. -/
set_option autoImplicit false

namespace LeanCrypto.Proofs.Groth16Codec

open LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fp
open LeanCrypto.Proofs.BN254Jacobian

theorem finite_g1_serialization_construct (proof : Types.ProofPoints) (b : G2.Affine)
    (aFinite : model proof.piA.z ≠ 0) (aCurve : ProjectiveEquation proof.piA)
    (cFinite : model proof.piC.z ≠ 0) (cCurve : ProjectiveEquation proof.piC)
    (bOutput : proof.piB.toAffine = .ok (some b)) :
    MSM.solidityProofBytes proof = .ok ⟨(encodeWords
      (affineLimbs (normalizedAffine proof.piA) b (normalizedAffine proof.piC))).toArray⟩ := by
  exact solidityProofBytes_construct proof _ b _
    (toAffine_finite_construct proof.piA aFinite aCurve) bOutput
    (toAffine_finite_construct proof.piC cFinite cCurve)

theorem finite_g1_serialization_shape (proof : Types.ProofPoints) (b : G2.Affine)
    (aFinite : model proof.piA.z ≠ 0) (aCurve : ProjectiveEquation proof.piA)
    (cFinite : model proof.piC.z ≠ 0) (cCurve : ProjectiveEquation proof.piC)
    (bOutput : proof.piB.toAffine = .ok (some b)) :
    ∃ bytes, MSM.solidityProofBytes proof = .ok bytes ∧ bytes.size = 256 ∧
      decodeWords 8 bytes.data.toList =
        affineLimbs (normalizedAffine proof.piA) b (normalizedAffine proof.piC) := by
  refine ⟨_, finite_g1_serialization_construct proof b aFinite aCurve cFinite cCurve bOutput, ?_, ?_⟩
  · simp [ByteArray.size, encodeWords_length, affineLimbs]
  · change decodeWords 8 (encodeWords _) = _
    have bounds : ∀ value, value ∈ affineLimbs (normalizedAffine proof.piA) b
        (normalizedAffine proof.piC) → value < 256 ^ 32 := by
      simpa using affine_limb_bounds (normalizedAffine proof.piA) b (normalizedAffine proof.piC)
    exact decodeWords_encodeWords _ bounds

theorem serialization_rejects_canonical_a_infinity (proof : Types.ProofPoints)
    (aInfinity : proof.piA = G1.Jacobian.infinity) :
    MSM.solidityProofBytes proof = .error "Groth16 A proof point is at infinity." := by
  simp only [MSM.solidityProofBytes, aInfinity, toAffine_infinity_construct, bind, Except.bind]
  rfl

theorem serialization_rejects_canonical_c_infinity (proof : Types.ProofPoints) (b : G2.Affine)
    (aFinite : model proof.piA.z ≠ 0) (aCurve : ProjectiveEquation proof.piA)
    (bOutput : proof.piB.toAffine = .ok (some b))
    (cInfinity : proof.piC = G1.Jacobian.infinity) :
    MSM.solidityProofBytes proof = .error "Groth16 C proof point is at infinity." := by
  simp only [MSM.solidityProofBytes, toAffine_finite_construct proof.piA aFinite aCurve,
    bOutput, cInfinity, toAffine_infinity_construct, bind, Except.bind]
  rfl

end LeanCrypto.Proofs.Groth16Codec

#print axioms LeanCrypto.Proofs.Groth16Codec.finite_g1_serialization_construct
#print axioms LeanCrypto.Proofs.Groth16Codec.finite_g1_serialization_shape
#print axioms LeanCrypto.Proofs.Groth16Codec.serialization_rejects_canonical_a_infinity
#print axioms LeanCrypto.Proofs.Groth16Codec.serialization_rejects_canonical_c_infinity
