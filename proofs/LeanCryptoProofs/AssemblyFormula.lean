import LeanCryptoProofs.AssemblyScalars
import LeanCryptoProofs.QapSetupAlgebra

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace LeanCrypto.Proofs.Groth16Assembly

open LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Proofs.WindowedMSM

noncomputable def aOffset (values : QueryScalars) (witness : Array Nat) : Fr :=
  values.alpha + linearScalar values.a witness witness.size
noncomputable def bOffset (values : QueryScalars) (witness : Array Nat) : Fr :=
  values.beta + linearScalar values.b witness witness.size
noncomputable def kOffset (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) : Fr :=
  linearScalar values.c (witness.extract (key.nPublic + 1) witness.size) key.queryC.size +
    linearScalar values.h h h.size

noncomputable def scalarOutput (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (r s : Nat) : IdealGroth16.Triple Fr :=
  let a := aOffset values witness + (r : Fr) * values.delta
  let b := bOffset values witness + (s : Fr) * values.delta
  ⟨a, b, kOffset key values witness h + (s : Fr) * a + (r : Fr) * b -
    (r : Fr) * (s : Fr) * values.delta⟩

theorem addG1_scalar (left right : G1.Jacobian) (x y : Fr)
    (leftAdmitted : G1Admitted left) (rightAdmitted : G1Admitted right)
    (first : g1 left = scalarG1 x) (second : g1 right = scalarG1 y) :
    g1 (left.add right) = scalarG1 (x + y) := by
  change LeanCrypto.Proofs.BN254Group.groupPoint (left.add right) = _
  rw [LeanCrypto.Proofs.BN254Group.add_groupPoint left right leftAdmitted rightAdmitted]
  change g1 left + g1 right = _
  rw [first, second, map_add]

theorem addG2_scalar (left right : G2.Jacobian) (x y : Fr)
    (leftAdmitted : G2Admitted left) (rightAdmitted : G2Admitted right)
    (first : g2 left = scalarG2 x) (second : g2 right = scalarG2 y) :
    g2 (left.add right) = scalarG2 (x + y) := by
  change LeanCrypto.Proofs.BN254G2Group.groupPoint (left.add right) = _
  rw [LeanCrypto.Proofs.BN254G2Group.add_groupPoint left right leftAdmitted rightAdmitted]
  change g2 left + g2 right = _
  rw [first, second, map_add]

/-- Source construction of A, B and C represents precisely the three
standard Groth16 scalar expressions, including all native reduction and
negative-rs details. Independent decoded-query relations are explicit. -/
theorem construction_scalarOutput (key : Types.QueryKey) (values : QueryScalars)
    (witness h : Array Nat) (r s : Nat) (valid : ValidKey key)
    (dimensions : Dimensions key witness h) (canonical : Canonical witness h r s)
    (span : KeySpan key values) :
    g1 (construction key witness h r s).piA =
        scalarG1 (scalarOutput key values witness h r s).a ∧
      g2 (construction key witness h r s).piB =
        scalarG2 (scalarOutput key values witness h r s).b ∧
      g1 (construction key witness h r s).piC =
        scalarG1 (scalarOutput key values witness h r s).c := by
  have add1 := LeanCrypto.Proofs.BN254Jacobian.add_preserves_curve_certified
  have mul1 := LeanCrypto.Proofs.BN254Group.scalarMul_admissible
  have add2 := LeanCrypto.Proofs.BN254G2Jacobian.add_admissible
  have mul2 := LeanCrypto.Proofs.BN254G2Group.scalarMul_admissible
  have da := decodedG1_admitted _ valid.alpha
  have db1 := decodedG1_admitted _ valid.beta1
  have dd1 := decodedG1_admitted _ valid.delta1
  have db2 := decodedG2_admitted _ valid.beta2
  have dd2 := decodedG2_admitted _ valid.delta2
  have as1 := sumG1_admitted _ witness valid.queryA
  have bs1 := sumG1_admitted _ witness valid.queryB1
  have bs2 := sumG2_admitted _ witness valid.queryB2
  have am : g1 (sumG1 key.queryA witness) =
      scalarG1 (linearScalar values.a witness witness.size) := by
    simpa only [dimensions.queryA] using
      sumG1_scalar key.queryA witness values.a dimensions.queryA canonical.witness valid.queryA span.queryA
  have b1m : g1 (sumG1 key.queryB1 witness) =
      scalarG1 (linearScalar values.b witness witness.size) := by
    simpa only [dimensions.queryB1] using
      sumG1_scalar key.queryB1 witness values.b dimensions.queryB1 canonical.witness valid.queryB1 span.queryB1
  have b2m : g2 (sumG2 key.queryB2 witness) =
      scalarG2 (linearScalar values.b witness witness.size) := by
    simpa only [dimensions.queryB2] using
      sumG2_scalar key.queryB2 witness values.b dimensions.queryB2 canonical.witness valid.queryB2 span.queryB2
  have a := addG1_scalar _ _ _ _ (add1 _ _ as1 da) (mul1 _ r dd1)
    (addG1_scalar _ _ _ _ as1 da am span.alpha)
    (scalarG1_native _ r values.delta dd1 span.delta1)
  have b := addG2_scalar _ _ _ _ (add2 _ _ bs2 db2) (mul2 _ s dd2)
    (addG2_scalar _ _ _ _ bs2 db2 b2m span.beta2)
    (scalarG2_native _ s values.delta dd2 span.delta2)
  have b1 := addG1_scalar _ _ _ _ (add1 _ _ bs1 db1) (mul1 _ s dd1)
    (addG1_scalar _ _ _ _ bs1 db1 b1m span.beta1)
    (scalarG1_native _ s values.delta dd1 span.delta1)
  have aExact : g1 (construction key witness h r s).piA =
      scalarG1 (scalarOutput key values witness h r s).a := by
    convert a using 1
    congr 1
    dsimp only [scalarOutput, aOffset]
    ring
  have bExact : g2 (construction key witness h r s).piB =
      scalarG2 (scalarOutput key values witness h r s).b := by
    convert b using 1
    congr 1
    dsimp only [scalarOutput, bOffset]
    ring
  have b1Exact : g1 (((sumG1 key.queryB1 witness).add (decodedG1Value key.vkBeta1)).add
      ((decodedG1Value key.vkDelta1).scalarMul s)) =
      scalarG1 (scalarOutput key values witness h r s).b := by
    convert b1 using 1
    congr 1
    dsimp only [scalarOutput, bOffset]
    ring
  have cs := sumG1_admitted _ (witness.extract (key.nPublic + 1) witness.size) valid.queryC
  have hs := sumG1_admitted _ h (extract_valid key.hExps ValidG1 valid.hExps 0 h.size)
  have privateShape : key.queryC.size = (witness.extract (key.nPublic + 1) witness.size).size := by
    simp [dimensions.queryC]
  have hShape : (key.hExps.extract 0 h.size).size = h.size := by
    simp [Nat.min_eq_left dimensions.hExps]
  have cm := sumG1_scalar key.queryC _ values.c privateShape
    (extract_canonical witness canonical.witness _ _) valid.queryC span.queryC
  have hm := sumG1_scalar (key.hExps.extract 0 h.size) h values.h hShape canonical.h
    (extract_valid key.hExps ValidG1 valid.hExps 0 h.size)
    (extract_initial_span key.hExps values.h span.hExps h.size dimensions.hExps)
  rw [hShape] at hm
  obtain ⟨aa, _, _⟩ := construction_admitted key witness h r s valid
  have b1Admitted := add1 _ _ (add1 _ _ bs1 db1) (mul1 _ s dd1)
  have c := addG1_scalar _ _ _ _
    (add1 _ _ (add1 _ _ (add1 _ _ cs hs) (mul1 _ s aa)) (mul1 _ r b1Admitted))
    (mul1 _ _ dd1)
    (addG1_scalar _ _ _ _ (add1 _ _ (add1 _ _ cs hs) (mul1 _ s aa))
      (mul1 _ r b1Admitted)
      (addG1_scalar _ _ _ _ (add1 _ _ cs hs) (mul1 _ s aa)
        (addG1_scalar _ _ _ _ cs hs cm hm)
        (scalarG1_native _ s _ aa aExact))
      (scalarG1_native _ r _ b1Admitted b1Exact))
    (scalarG1_native _ ((MSM.order - (r * s % MSM.order)) % MSM.order)
      values.delta dd1 span.delta1)
  refine ⟨aExact, bExact, ?_⟩
  convert c using 1
  congr 1
  rw [minusRS_model]
  dsimp only [scalarOutput, kOffset]
  ring

end LeanCrypto.Proofs.Groth16Assembly

#print axioms LeanCrypto.Proofs.Groth16Assembly.addG1_scalar
#print axioms LeanCrypto.Proofs.Groth16Assembly.addG2_scalar
#print axioms LeanCrypto.Proofs.Groth16Assembly.construction_scalarOutput
