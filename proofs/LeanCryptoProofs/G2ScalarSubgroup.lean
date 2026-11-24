import LeanCryptoProofs.G2Subgroup
import LeanCryptoProofs.G2NormalizationGroupLaw
import LeanCryptoProofs.ScalarSubgroup

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254G2Group
open LeanCrypto.BN254.G2 BN254G2Jacobian
local instance : NeZero LeanCrypto.BN254.G1.scalarPrime := ⟨by decide +kernel⟩

theorem generator_exact_order :
    addOrderOf (groupPoint (Jacobian.ofAffine generator)) = LeanCrypto.BN254.G1.scalarPrime := by
  letI : Fact LeanCrypto.BN254.G1.scalarPrime.Prime := ⟨Primes.bn254_scalar_prime⟩
  exact addOrderOf_eq_prime generator_q_annihilates generator_nonzero

noncomputable def scalarHom : ZMod LeanCrypto.BN254.G1.scalarPrime →+ curve.toAffine.Point :=
  ScalarSubgroup.scalarHom (groupPoint (Jacobian.ofAffine generator)) generator_q_annihilates

theorem scalarHom_injective : Function.Injective scalarHom := by
  intro left right equal
  change left.val • groupPoint (Jacobian.ofAffine generator) =
    right.val • groupPoint (Jacobian.ofAffine generator) at equal
  have residues := nsmul_inj_mod.mp equal
  rw [generator_exact_order, Nat.mod_eq_of_lt left.val_lt, Nat.mod_eq_of_lt right.val_lt] at residues
  exact ZMod.val_injective _ residues

theorem affine_group_nonzero (point : Affine) (admitted : point.onCurve = true) :
    groupPoint (Jacobian.ofAffine point) ≠ 0 := by
  intro zero
  have infinite := (groupPoint_zero_iff _ (ofAffine_admissible point admitted)).1 zero
  have zEqual := congrArg (fun point : Jacobian => BN254Fp2.model point.z) infinite
  simp [Jacobian.ofAffine, Jacobian.infinity] at zEqual

theorem affine_checked_exact_order (point : Affine) (admitted : point.onCurve = true)
    (subgroup : ((Jacobian.ofAffine point).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true) :
    addOrderOf (groupPoint (Jacobian.ofAffine point)) = LeanCrypto.BN254.G1.scalarPrime := by
  letI : Fact LeanCrypto.BN254.G1.scalarPrime.Prime := ⟨Primes.bn254_scalar_prime⟩
  exact addOrderOf_eq_prime ((subgroup_check_iff _ (ofAffine_admissible point admitted)).1 subgroup)
    (affine_group_nonzero point admitted)

/-- Every proper positive Miller scalarPrefix stays finite for every actual input
passing the on-twist and unreduced subgroup check. -/
theorem affine_checked_prefix_nonzero (point : Affine) (admitted : point.onCurve = true)
    (subgroup : ((Jacobian.ofAffine point).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true)
    (scalarPrefix : Nat) (positive : 0 < scalarPrefix) (proper : scalarPrefix < LeanCrypto.BN254.G1.scalarPrime) :
    scalarPrefix • groupPoint (Jacobian.ofAffine point) ≠ 0 := by
  intro zero
  have equal : scalarPrefix • groupPoint (Jacobian.ofAffine point) =
      0 • groupPoint (Jacobian.ofAffine point) := by simpa using zero
  have residues := nsmul_inj_mod.mp equal
  rw [affine_checked_exact_order point admitted subgroup, Nat.mod_eq_of_lt proper, Nat.zero_mod] at residues
  omega

end LeanCrypto.Proofs.BN254G2Group
#print axioms LeanCrypto.Proofs.BN254G2Group.generator_exact_order
#print axioms LeanCrypto.Proofs.BN254G2Group.scalarHom_injective
#print axioms LeanCrypto.Proofs.BN254G2Group.affine_group_nonzero
#print axioms LeanCrypto.Proofs.BN254G2Group.affine_checked_exact_order
#print axioms LeanCrypto.Proofs.BN254G2Group.affine_checked_prefix_nonzero
