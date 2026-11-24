import LeanCryptoProofs.ScalarPairing
import LeanCrypto.Groth16.Verify

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.NativeVerifier
open LeanCrypto.BN254.G1 LeanCrypto.Groth16.Verify Groth16Assembly BN254Tate

theorem pair_scalar_construct (first : Affine) (second : LeanCrypto.BN254.G2.Affine)
    (firstCurve : first.onCurve = true) (secondCurve : second.onCurve = true)
    (a b : Fr) (firstSpan : BN254Group.affinePoint first firstCurve = scalarG1 a)
    (secondSpan : BN254G2Group.affinePoint second secondCurve = scalarG2 b) :
    ∃ result : LeanCrypto.BN254.PairingField.Fp12, LeanCrypto.BN254.TatePairing.pair first second = .ok result ∧
      BN254Fp12.model result = ((scalarPairHom a b).toMul : BN254Fp12.Field) := by
  have torsion : scalarPrime • BN254G2Group.affinePoint second secondCurve = 0 := by
    rw [secondSpan, scalarG2_q_torsion]
  obtain ⟨result, constructed, meaning⟩ := pair_construct_bilinear first second firstCurve secondCurve torsion
  refine ⟨result, constructed, ?_⟩
  rw [nativeTwistTorsion_scalar second secondCurve b secondSpan torsion, firstSpan] at meaning
  exact meaning

theorem negative_affinePoint (point : Affine) (onCurve : point.onCurve = true) :
    BN254Group.affinePoint (negativeNativeG1 point) (negativeNativeG1_onCurve point onCurve) =
      -BN254Group.affinePoint point onCurve := by
  unfold BN254Group.affinePoint negativeNativeG1
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp only [BN254Fp.model_neg]
  simp only [WeierstrassCurve.Affine.negY, BN254Group.curve, zero_mul, sub_zero]

/-- Constructive completeness of the original four native pairing calls.
The public-input call is attached by the separate original-loop construction. -/
theorem verify_construct_of_publicInput (key : VerifyingKey) (proof : Proof) (signals : Array Nat)
    (vkX : Affine) (inputCurve : vkX.onCurve = true)
    (publicInput : publicInputPoint key signals = .ok vkX)
    (aCurve : proof.a.onCurve = true) (bCurve : proof.b.onCurve = true) (cCurve : proof.c.onCurve = true)
    (alphaCurve : key.alpha1.onCurve = true) (betaCurve : key.beta2.onCurve = true)
    (gammaCurve : key.gamma2.onCurve = true) (deltaCurve : key.delta2.onCurve = true)
    (a b c alpha beta gamma delta publicIC : Fr)
    (aSpan : BN254Group.affinePoint proof.a aCurve = scalarG1 a)
    (bSpan : BN254G2Group.affinePoint proof.b bCurve = scalarG2 b)
    (cSpan : BN254Group.affinePoint proof.c cCurve = scalarG1 c)
    (alphaSpan : BN254Group.affinePoint key.alpha1 alphaCurve = scalarG1 alpha)
    (betaSpan : BN254G2Group.affinePoint key.beta2 betaCurve = scalarG2 beta)
    (gammaSpan : BN254G2Group.affinePoint key.gamma2 gammaCurve = scalarG2 gamma)
    (deltaSpan : BN254G2Group.affinePoint key.delta2 deltaCurve = scalarG2 delta)
    (inputSpan : BN254Group.affinePoint vkX inputCurve = scalarG1 publicIC)
    (equation : a * b = alpha * beta + publicIC * gamma + c * delta) :
    verify key proof signals = .ok true := by
  have negativeSpan : BN254Group.affinePoint (negativeNativeG1 proof.a)
      (negativeNativeG1_onCurve proof.a aCurve) = scalarG1 (-a) := by
    rw [negative_affinePoint proof.a aCurve, aSpan, map_neg]
  obtain ⟨e0, call0, meaning0⟩ := pair_scalar_construct _ proof.b (negativeNativeG1_onCurve proof.a aCurve)
    bCurve (-a) b negativeSpan bSpan
  obtain ⟨e1, call1, meaning1⟩ := pair_scalar_construct _ _ alphaCurve betaCurve alpha beta alphaSpan betaSpan
  obtain ⟨e2, call2, meaning2⟩ := pair_scalar_construct _ _ inputCurve gammaCurve publicIC gamma inputSpan gammaSpan
  obtain ⟨e3, call3, meaning3⟩ := pair_scalar_construct _ _ cCurve deltaCurve c delta cSpan deltaSpan
  have scalarEquation := scalar_verifier_equation a b c alpha beta gamma delta publicIC equation
  have fieldEquation := congrArg (fun value : Additive BN254Fp12.Fieldˣ => (value.toMul : BN254Fp12.Field)) scalarEquation
  have accepted : (((e0.mul e1).mul e2).mul e3 == LeanCrypto.BN254.PairingField.Fp12.one) = true := by
    apply (BN254Fp12.model_beq _ _).2
    simp only [BN254Fp12.model_mul, BN254Fp12.model_one, meaning0, meaning1, meaning2, meaning3]
    exact fieldEquation
  unfold verify
  rw [publicInput]
  change (do
    let v0 ← LeanCrypto.BN254.TatePairing.pair (negativeNativeG1 proof.a) proof.b
    let v1 ← LeanCrypto.BN254.TatePairing.pair key.alpha1 key.beta2
    let v2 ← LeanCrypto.BN254.TatePairing.pair vkX key.gamma2
    let v3 ← LeanCrypto.BN254.TatePairing.pair proof.c key.delta2
    return (((v0.mul v1).mul v2).mul v3) == LeanCrypto.BN254.PairingField.Fp12.one) = .ok true
  rw [call0, call1, call2, call3]
  exact congrArg Except.ok accepted

end LeanCrypto.Proofs.NativeVerifier
#print axioms LeanCrypto.Proofs.NativeVerifier.pair_scalar_construct
#print axioms LeanCrypto.Proofs.NativeVerifier.negative_affinePoint
#print axioms LeanCrypto.Proofs.NativeVerifier.verify_construct_of_publicInput
