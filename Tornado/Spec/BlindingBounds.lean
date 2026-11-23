import Tornado.Spec.BlindingPair

/-! Exact conservative production exhaustion bounds under the ideal decoded
IID entropy contract. A scalar's failure probability is at most2^-128;
failure of either sequential scalar is at most2^-127. These are sampler-only
bounds, excluding OS read failures and downstream proving failures. -/

namespace Tornado.Spec.BlindingDistribution

open Tornado.Runtime.ProofBlinding

def productionAlphabet : Nat := 2 ^ 256
def productionModulus : Nat := Tornado.Protocol.Groth16R1CS.scalarPrime

theorem production_modulus_fits : 1 < productionModulus ∧ productionModulus ≤ productionAlphabet := by
  decide

/-- A short exact integer comparison is raised symbolically to512 trials;
the kernel never enumerates a 256-bit alphabet or its draw streams. -/
theorem production_four_draw_bound :
    2 * retryCount productionAlphabet productionModulus ^ 4 ≤ productionAlphabet ^ 4 := by
  decide

theorem production_scalar_exhaustion_bound :
    mass productionAlphabet productionModulus maxAttempts failureEvent * 2 ^ 128 ≤
      productionAlphabet ^ maxAttempts := by
  rw [exhaustion_count _ _ _ (by have h := production_modulus_fits; omega)
    production_modulus_fits.2]
  have raised := Nat.pow_le_pow_left production_four_draw_bound 128
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at raised
  simpa only [maxAttempts, show 4 * 128 = 512 by decide, Nat.mul_comm] using raised

theorem pair_failure_le_two_single (D q budget : Nat)
    (positive : 0 < q) (fits : q ≤ D) :
    pairMass D q budget failureEvent ≤ 2 * retryCount D q ^ budget * D ^ budget := by
  have norm := normalization D q budget positive fits
  have pairNorm := pair_normalization D q budget
  rw [pair_success_count, success_count D q budget positive fits] at pairNorm
  have identity :
      ((q - 1) * successWeight D q budget) ^ 2 +
        2 * retryCount D q ^ budget * D ^ budget =
      D ^ (budget + budget) + (retryCount D q ^ budget) ^ 2 := by
    have algebra (a b : Nat) : a * a + 2 * b * (a + b) =
        (a + b) * (a + b) + b * b := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
      have cross := Nat.mul_comm a b
      omega
    rw [Nat.pow_add, ← norm]
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul] using
      algebra ((q - 1) * successWeight D q budget) (retryCount D q ^ budget)
  omega

theorem production_pair_exhaustion_bound :
    pairMass productionAlphabet productionModulus maxAttempts failureEvent * 2 ^ 127 ≤
      productionAlphabet ^ (maxAttempts + maxAttempts) := by
  have single := production_scalar_exhaustion_bound
  have pair := pair_failure_le_two_single productionAlphabet productionModulus maxAttempts
    (by have h := production_modulus_fits; omega) production_modulus_fits.2
  have lifted := Nat.mul_le_mul_right (2 ^ 127) pair
  rw [exhaustion_count _ _ _ (by have h := production_modulus_fits; omega)
    production_modulus_fits.2] at single
  calc
    _ ≤ (2 * retryCount productionAlphabet productionModulus ^ maxAttempts *
        productionAlphabet ^ maxAttempts) * 2 ^ 127 := lifted
    _ = (retryCount productionAlphabet productionModulus ^ maxAttempts * 2 ^ 128) *
        productionAlphabet ^ maxAttempts := by
      have reorder (a b c : Nat) : (2 * a * b) * c = (a * (2 * c)) * b := by ac_rfl
      rw [← show (2 : Nat) * 2 ^ 127 = 2 ^ 128 by decide]
      exact reorder _ _ _
    _ ≤ (productionAlphabet ^ maxAttempts) * productionAlphabet ^ maxAttempts :=
      Nat.mul_le_mul_right _ single
    _ = _ := (Nat.pow_add _ _ _).symm

end Tornado.Spec.BlindingDistribution

#print axioms Tornado.Spec.BlindingDistribution.production_modulus_fits
#print axioms Tornado.Spec.BlindingDistribution.production_four_draw_bound
#print axioms Tornado.Spec.BlindingDistribution.production_scalar_exhaustion_bound
#print axioms Tornado.Spec.BlindingDistribution.pair_failure_le_two_single
#print axioms Tornado.Spec.BlindingDistribution.production_pair_exhaustion_bound
