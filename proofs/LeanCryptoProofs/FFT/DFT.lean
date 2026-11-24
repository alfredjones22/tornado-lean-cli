import LeanCryptoProofs.CertifiedFields
import LeanCryptoProofs.RootConstruction
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Proofs.BN254Fr

abbrev Fr := ZMod Q

/-- Independent finite-field DFT specification, without any bit reversal,
butterfly, mutable array, or source transform definition. -/
def dft (size : Nat) (root : Fr) (input : Nat → Fr) (index : Nat) : Fr :=
  ∑ coefficient ∈ Finset.range size, input coefficient * root ^ (index * coefficient)

def inverseDft (size : Nat) (root : Fr) (input : Nat → Fr) (index : Nat) : Fr :=
  (size : Fr)⁻¹ * dft size root⁻¹ input index

def domainRoot (size : Nat) : Fr := model (constructedRoot size)

theorem domainRoot_primitive (size : Nat) (admitted : LeanCrypto.Groth16.FFT.validSize size = true) :
    IsPrimitiveRoot (domainRoot size) size := by
  rw [IsPrimitiveRoot.iff_orderOf]
  exact admitted_root_exact_order size admitted

theorem domain_size_nonzero (size : Nat) (admitted : LeanCrypto.Groth16.FFT.validSize size = true) :
    (size : Fr) ≠ 0 := by
  have requirements := admitted
  simp only [LeanCrypto.Groth16.FFT.validSize, LeanCrypto.Groth16.FFT.maximumSize,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at requirements
  have positive : 0 < size := by omega
  have bounded : size < Q := by
    have : 65536 < Q := by decide
    omega
  change model size ≠ 0
  intro zero
  have nativeZero := (model_zero_iff size).1 zero
  rw [Nat.mod_eq_of_lt bounded] at nativeZero
  omega

theorem primitive_half_neg_one (root : Fr) (bits : Nat)
    (primitive : IsPrimitiveRoot root (2 ^ (bits + 1))) :
    root ^ (2 ^ bits) = -1 := by
  have square : (root ^ (2 ^ bits)) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ]
    exact primitive.pow_eq_one
  have different : root ^ (2 ^ bits) ≠ 1 := by
    apply primitive.pow_ne_one_of_pos_of_lt
    · exact Nat.ne_of_gt (pow_pos (by decide) _)
    · rw [pow_succ]
      have positive : 0 < 2 ^ bits := pow_pos (by decide) _
      omega
  exact (sq_eq_one_iff.mp square).resolve_left different

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.domainRoot_primitive
#print axioms LeanCrypto.Proofs.FFT.domain_size_nonzero
#print axioms LeanCrypto.Proofs.FFT.primitive_half_neg_one
