import LeanCryptoProofs.NormalizationUniqueness
set_option autoImplicit false

namespace LeanCrypto.Proofs.Groth16Assembly

open LeanCrypto.BN254 LeanCrypto.Groth16
local instance : NeZero G1.scalarPrime := ⟨by decide⟩

/-- Canonical native representatives for a scalar triple. This is a proof
observer, not another prover or an assumed serializer specification. -/
def canonicalPoints (signals : Array Nat) (triple : IdealGroth16.Triple Fr) : Types.ProofPoints :=
  ⟨(G1.Jacobian.ofAffine G1.generator).scalarMul triple.a.val,
    (G2.Jacobian.ofAffine G2.generator).scalarMul triple.b.val,
    (G1.Jacobian.ofAffine G1.generator).scalarMul triple.c.val, signals⟩

theorem canonical_g1 (value : Fr) :
    g1 ((G1.Jacobian.ofAffine G1.generator).scalarMul value.val) = scalarG1 value := by
  change LeanCrypto.Proofs.BN254Group.groupPoint _ = _
  rw [LeanCrypto.Proofs.BN254Group.scalarMul_canonical_groupPoint _ _
    LeanCrypto.Proofs.BN254Jacobian.generator_admissible value.val_lt]
  rfl

theorem canonical_g2 (value : Fr) :
    g2 ((G2.Jacobian.ofAffine G2.generator).scalarMul value.val) = scalarG2 value := by
  change LeanCrypto.Proofs.BN254G2Group.groupPoint _ = _
  rw [LeanCrypto.Proofs.BN254G2Group.scalarMul_groupPoint _ _
    LeanCrypto.Proofs.BN254G2Jacobian.generator_admissible]
  rfl

theorem canonical_admitted (signals : Array Nat) (triple : IdealGroth16.Triple Fr) :
    G1Admitted (canonicalPoints signals triple).piA ∧
      G2Admitted (canonicalPoints signals triple).piB ∧
      G1Admitted (canonicalPoints signals triple).piC :=
  ⟨LeanCrypto.Proofs.BN254Group.scalarMul_admissible _ _
      LeanCrypto.Proofs.BN254Jacobian.generator_admissible,
    LeanCrypto.Proofs.BN254G2Group.scalarMul_admissible _ _
      LeanCrypto.Proofs.BN254G2Jacobian.generator_admissible,
    LeanCrypto.Proofs.BN254Group.scalarMul_admissible _ _
      LeanCrypto.Proofs.BN254Jacobian.generator_admissible⟩

theorem normalization_factors_through_triple (points : Types.ProofPoints)
    (triple : IdealGroth16.Triple Fr) (signals : Array Nat)
    (a : G1Admitted points.piA) (b : G2Admitted points.piB) (c : G1Admitted points.piC)
    (aMeaning : g1 points.piA = scalarG1 triple.a)
    (bMeaning : g2 points.piB = scalarG2 triple.b)
    (cMeaning : g1 points.piC = scalarG1 triple.c) :
    points.piA.toAffine = (canonicalPoints signals triple).piA.toAffine ∧
      points.piB.toAffine = (canonicalPoints signals triple).piB.toAffine ∧
      points.piC.toAffine = (canonicalPoints signals triple).piC.toAffine := by
  obtain ⟨ca, cb, cc⟩ := canonical_admitted signals triple
  exact ⟨g1_normalization_unique _ _ a ca (aMeaning.trans (canonical_g1 triple.a).symm),
    g2_normalization_unique _ _ b cb (bMeaning.trans (canonical_g2 triple.b).symm),
    g1_normalization_unique _ _ c cc (cMeaning.trans (canonical_g1 triple.c).symm)⟩

/-- Exact native serializer, including its failure outcome, is a common
deterministic function of the mathematical triple. No acceptance condition
or infinity failure is discarded by this equality. -/
theorem serialization_factors_through_triple (points : Types.ProofPoints)
    (triple : IdealGroth16.Triple Fr) (signals : Array Nat)
    (a : G1Admitted points.piA) (b : G2Admitted points.piB) (c : G1Admitted points.piC)
    (aMeaning : g1 points.piA = scalarG1 triple.a)
    (bMeaning : g2 points.piB = scalarG2 triple.b)
    (cMeaning : g1 points.piC = scalarG1 triple.c) :
    MSM.solidityProofBytes points = MSM.solidityProofBytes (canonicalPoints signals triple) := by
  obtain ⟨ha, hb, hc⟩ := normalization_factors_through_triple points triple signals
    a b c aMeaning bMeaning cMeaning
  unfold MSM.solidityProofBytes
  rw [ha, hb, hc]

/-- Implementation-level output factorization, before attachment of the
QAP compatibility identity and before the actual worker terminal pipeline. -/
theorem assembly_serialization_factors (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (r s : Nat) (valid : ValidKey key)
    (dimensions : Dimensions key witness h) (canonical : Canonical witness h r s)
    (span : KeySpan key values) :
    MSM.solidityProofBytes (construction key witness h r s) =
      MSM.solidityProofBytes (canonicalPoints (witness.extract 1 (key.nPublic + 1))
        (scalarOutput key values witness h r s)) := by
  obtain ⟨a, b, c⟩ := construction_admitted key witness h r s valid
  obtain ⟨am, bm, cm⟩ := construction_scalarOutput key values witness h r s valid dimensions canonical span
  exact serialization_factors_through_triple _ _ _ a b c am bm cm

end LeanCrypto.Proofs.Groth16Assembly

#print axioms LeanCrypto.Proofs.Groth16Assembly.canonical_g1
#print axioms LeanCrypto.Proofs.Groth16Assembly.canonical_g2
#print axioms LeanCrypto.Proofs.Groth16Assembly.canonical_admitted
#print axioms LeanCrypto.Proofs.Groth16Assembly.normalization_factors_through_triple
#print axioms LeanCrypto.Proofs.Groth16Assembly.serialization_factors_through_triple
#print axioms LeanCrypto.Proofs.Groth16Assembly.assembly_serialization_factors
