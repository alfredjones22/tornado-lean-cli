import LeanCryptoProofs.G2ScalarMulGroupLaw
import LeanCryptoProofs.G2GeneratorOrder

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254G2Group
open LeanCrypto.BN254.G2 LeanCrypto.Proofs.BN254G2Jacobian

/-- The actual unreduced native subgroup check is precisely the q-torsion
condition in the independently established curve group. -/
theorem subgroup_check_iff (point : Jacobian) (admitted : Admissible point) :
    (point.scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true ↔
      LeanCrypto.BN254.G1.scalarPrime • groupPoint point = 0 := by
  rw [← scalarMul_groupPoint point _ admitted, groupPoint_zero_iff _ (scalarMul_admissible point _ admitted)]
  constructor
  · exact admissible_infinity _ (scalarMul_admissible point _ admitted)
  · intro equal
    rw [equal]
    rfl

theorem generator_q_annihilates :
    LeanCrypto.BN254.G1.scalarPrime • groupPoint (Jacobian.ofAffine generator) = 0 :=
  (subgroup_check_iff _ generator_admissible).1 BN254G2Order.generator_public_q_order

theorem generator_nonzero : groupPoint (Jacobian.ofAffine generator) ≠ 0 := by
  intro zero
  have impossible := (groupPoint_zero_iff _ generator_admissible).1 zero
  have zEqual := congrArg Jacobian.z impossible
  have models := congrArg LeanCrypto.Proofs.BN254Fp2.model zEqual
  simp [Jacobian.ofAffine, Jacobian.infinity] at models

end LeanCrypto.Proofs.BN254G2Group
#print axioms LeanCrypto.Proofs.BN254G2Group.subgroup_check_iff
#print axioms LeanCrypto.Proofs.BN254G2Group.generator_q_annihilates
#print axioms LeanCrypto.Proofs.BN254G2Group.generator_nonzero
