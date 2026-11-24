import LeanCryptoProofs.WindowedMSM.Horner

set_option autoImplicit false

namespace LeanCrypto.Proofs.WindowedMSM

variable {G : Type} [AddCommMonoid G] [Inhabited G]

/-- The actual generic window/bucket implementation computes the weighted
sum when instantiated with established additive-monoid operations. Native
Jacobian operations still require a separate representation transport. -/
theorem native_group_sum (points : Array G) (scalars : Array Nat)
    (canonical : ∀ index, index < points.size → scalars[index]! < LeanCrypto.Groth16.MSM.order) :
    nativeWindowed points scalars 0 (· + ·) (fun point => point + point) =
      ∑ index ∈ Finset.range points.size, scalars[index]! • points[index]! := by
  rw [native_group_horner, reverseHorner_sum]
  simp only [nsmul_zero, zero_add]
  simp_rw [← Finset.sum_nsmul, ← mul_nsmul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index member
  rw [← Finset.sum_smul]
  apply congrArg (fun scalar : Nat => scalar • points[index]!)
  have digits := native_digits_reconstruct scalars[index]! points.size
    (canonical index (Finset.mem_range.mp member))
  simpa only [radix, ← pow_mul, Nat.mul_comm] using digits

end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.native_group_sum
