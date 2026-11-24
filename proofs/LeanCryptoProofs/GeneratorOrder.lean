import LeanCryptoProofs.ScalarMulNormalization
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 32768

namespace LeanCrypto.Proofs.BN254Group

open LeanCrypto.BN254.G1 LeanCrypto.Proofs.BN254Jacobian

/-- This evaluates the unreduced backend at q, rather than the public
scalar function whose initial reduction would make the check vacuous. -/
theorem generator_unreduced_order_check :
    (Jacobian.scalarMulLoop (Jacobian.ofAffine generator) scalarPrime
      Jacobian.infinity).isInfinity = true := by
  decide +kernel

theorem generator_order_annihilates :
    scalarPrime • groupPoint (Jacobian.ofAffine generator) = 0 := by
  have admitted := scalarMulLoop_admissible (Jacobian.ofAffine generator)
    Jacobian.infinity scalarPrime generator_admissible infinity_admissible
  have infinite := admissible_infinity _ admitted generator_unreduced_order_check
  have meaning := scalarMulLoop_groupPoint (Jacobian.ofAffine generator)
    Jacobian.infinity scalarPrime generator_admissible infinity_admissible
  rw [infinite, infinity_groupPoint, zero_add] at meaning
  exact meaning.symm

theorem generator_group_nonzero : groupPoint (Jacobian.ofAffine generator) ≠ 0 := by
  intro zero
  have infinite := (groupPoint_zero_iff _ generator_admissible).mp zero
  have z := congrArg (fun point : Jacobian => point.z.val) infinite
  norm_num [Jacobian.ofAffine, Jacobian.infinity, Fp.one, Fp.zero, Fp.ofNat] at z
  exact (by decide : basePrime ≠ 1) z

theorem generator_exact_order :
    addOrderOf (groupPoint (Jacobian.ofAffine generator)) = scalarPrime := by
  letI : Fact scalarPrime.Prime := ⟨Primes.bn254_scalar_prime⟩
  exact addOrderOf_eq_prime generator_order_annihilates generator_group_nonzero

end LeanCrypto.Proofs.BN254Group

#print axioms LeanCrypto.Proofs.BN254Group.generator_unreduced_order_check
#print axioms LeanCrypto.Proofs.BN254Group.generator_order_annihilates
#print axioms LeanCrypto.Proofs.BN254Group.generator_group_nonzero
#print axioms LeanCrypto.Proofs.BN254Group.generator_exact_order
