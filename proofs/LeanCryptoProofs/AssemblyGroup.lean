import LeanCryptoProofs.AssemblySource
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanCrypto.Proofs.Groth16Assembly

open LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Proofs.WindowedMSM

abbrev G1Admitted := LeanCrypto.Proofs.BN254Jacobian.Admissible
abbrev G2Admitted := LeanCrypto.Proofs.BN254G2Jacobian.Admissible
noncomputable abbrev g1 := LeanCrypto.Proofs.BN254Group.groupPoint
noncomputable abbrev g2 := LeanCrypto.Proofs.BN254G2Group.groupPoint

theorem decodedG1_admitted (input : Types.DecodedG1) (valid : ValidG1 input) :
    G1Admitted (decodedG1Value input) :=
  nativeG1Point_admissible input _ (nativeG1Point_construct input valid)

theorem decodedG2_admitted (input : Types.DecodedG2) (valid : ValidG2 input) :
    G2Admitted (decodedG2Value input) :=
  nativeG2Point_admissible input _ (nativeG2Point_construct input valid)

theorem mappedG1_admitted (points : Array Types.DecodedG1)
    (valid : ∀ point ∈ points, ValidG1 point) :
    ∀ point ∈ points.map decodedG1Value, G1Admitted point := by
  intro point member
  obtain ⟨input, original, rfl⟩ := Array.mem_map.mp member
  exact decodedG1_admitted input (valid input original)

theorem mappedG2_admitted (points : Array Types.DecodedG2)
    (valid : ∀ point ∈ points, ValidG2 point) :
    ∀ point ∈ points.map decodedG2Value, G2Admitted point := by
  intro point member
  obtain ⟨input, original, rfl⟩ := Array.mem_map.mp member
  exact decodedG2_admitted input (valid input original)

theorem sumG1_admitted (points : Array Types.DecodedG1) (scalars : Array Nat)
    (valid : ∀ point ∈ points, ValidG1 point) : G1Admitted (sumG1 points scalars) :=
  native_g1_raw_windowed_admissible _ scalars (mappedG1_admitted points valid)

theorem sumG2_admitted (points : Array Types.DecodedG2) (scalars : Array Nat)
    (valid : ∀ point ∈ points, ValidG2 point) : G2Admitted (sumG2 points scalars) :=
  native_g2_raw_windowed_admissible _ scalars (mappedG2_admitted points valid)

theorem scalar_bound (pointsSize : Nat) (scalars : Array Nat) (counts : pointsSize = scalars.size)
    (canonical : scalars.all (· < MSM.order) = true) :
    ∀ index, index < pointsSize → scalars[index]! < MSM.order := by
  intro index bounded
  have bound : index < scalars.size := by omega
  have value := Array.all_eq_true.mp canonical index bound
  simpa [bound] using value

theorem sumG1_group (points : Array Types.DecodedG1) (scalars : Array Nat)
    (counts : points.size = scalars.size)
    (canonical : scalars.all (· < MSM.order) = true)
    (valid : ∀ point ∈ points, ValidG1 point) :
    g1 (sumG1 points scalars) = ∑ index ∈ Finset.range points.size,
      scalars[index]! • g1 (decodedG1Value points[index]!) := by
  have meaning := native_g1_raw_windowed_sum (points.map decodedG1Value) scalars
    (mappedG1_admitted points valid) (by simpa using scalar_bound _ scalars counts canonical)
  simpa only [Array.size_map, map_getBang decodedG1Value rfl] using meaning

theorem sumG2_group (points : Array Types.DecodedG2) (scalars : Array Nat)
    (counts : points.size = scalars.size)
    (canonical : scalars.all (· < MSM.order) = true)
    (valid : ∀ point ∈ points, ValidG2 point) :
    g2 (sumG2 points scalars) = ∑ index ∈ Finset.range points.size,
      scalars[index]! • g2 (decodedG2Value points[index]!) := by
  have meaning := native_g2_raw_windowed_sum (points.map decodedG2Value) scalars
    (mappedG2_admitted points valid) (by simpa using scalar_bound _ scalars counts canonical)
  simpa only [Array.size_map, map_getBang decodedG2Value rfl] using meaning

theorem construction_admitted (key : Types.QueryKey) (witness h : Array Nat) (r s : Nat)
    (valid : ValidKey key) :
    G1Admitted (construction key witness h r s).piA ∧
      G2Admitted (construction key witness h r s).piB ∧
      G1Admitted (construction key witness h r s).piC := by
  have add1 := LeanCrypto.Proofs.BN254Jacobian.add_preserves_curve_certified
  have add2 := LeanCrypto.Proofs.BN254G2Jacobian.add_admissible
  have scalar1 := LeanCrypto.Proofs.BN254Group.scalarMul_admissible
  have scalar2 := LeanCrypto.Proofs.BN254G2Group.scalarMul_admissible
  have a : G1Admitted (construction key witness h r s).piA :=
    add1 _ _ (add1 _ _ (sumG1_admitted _ _ valid.queryA)
      (decodedG1_admitted _ valid.alpha)) (scalar1 _ r (decodedG1_admitted _ valid.delta1))
  have b : G2Admitted (construction key witness h r s).piB :=
    add2 _ _ (add2 _ _ (sumG2_admitted _ _ valid.queryB2)
      (decodedG2_admitted _ valid.beta2)) (scalar2 _ s (decodedG2_admitted _ valid.delta2))
  have b1 := add1 _ _ (add1 _ _ (sumG1_admitted _ witness valid.queryB1)
    (decodedG1_admitted _ valid.beta1)) (scalar1 _ s (decodedG1_admitted _ valid.delta1))
  refine ⟨a, b, ?_⟩
  exact add1 _ _ (add1 _ _ (add1 _ _
    (add1 _ _ (sumG1_admitted _ _ valid.queryC)
      (sumG1_admitted _ _ (extract_valid key.hExps ValidG1 valid.hExps _ _)))
    (scalar1 _ s a)) (scalar1 _ r b1))
    (scalar1 _ _ (decodedG1_admitted _ valid.delta1))

end LeanCrypto.Proofs.Groth16Assembly

#print axioms LeanCrypto.Proofs.Groth16Assembly.decodedG1_admitted
#print axioms LeanCrypto.Proofs.Groth16Assembly.decodedG2_admitted
#print axioms LeanCrypto.Proofs.Groth16Assembly.mappedG1_admitted
#print axioms LeanCrypto.Proofs.Groth16Assembly.mappedG2_admitted
#print axioms LeanCrypto.Proofs.Groth16Assembly.sumG1_admitted
#print axioms LeanCrypto.Proofs.Groth16Assembly.sumG2_admitted
#print axioms LeanCrypto.Proofs.Groth16Assembly.scalar_bound
#print axioms LeanCrypto.Proofs.Groth16Assembly.sumG1_group
#print axioms LeanCrypto.Proofs.Groth16Assembly.sumG2_group
#print axioms LeanCrypto.Proofs.Groth16Assembly.construction_admitted
