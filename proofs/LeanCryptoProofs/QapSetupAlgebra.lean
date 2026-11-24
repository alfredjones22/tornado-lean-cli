import LeanCryptoProofs.Groth16IdealPrivacy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace LeanCrypto.Proofs.Groth16Setup

open scoped BigOperators

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

def weighted (weights values : ι → F) : F := ∑ index, weights index * values index

def contribution (alpha beta : F) (u v w : ι → F) (index : ι) : F :=
  beta * u index + alpha * v index + w index

def publicCombined (publicIndices : Finset ι) (weights : ι → F) (alpha beta : F)
    (u v w : ι → F) : F :=
  ∑ index ∈ publicIndices, weights index * contribution alpha beta u v w index

def privateCombined (publicIndices : Finset ι) (weights : ι → F) (alpha beta : F)
    (u v w : ι → F) : F :=
  ∑ index ∈ Finset.univ \ publicIndices, weights index * contribution alpha beta u v w index

theorem combined_partition (publicIndices : Finset ι) (weights : ι → F) (alpha beta : F)
    (u v w : ι → F) :
    publicCombined publicIndices weights alpha beta u v w +
      privateCombined publicIndices weights alpha beta u v w =
      beta * weighted weights u + alpha * weighted weights v + weighted weights w := by
  classical
  have partition := Finset.sum_sdiff (Finset.subset_univ publicIndices)
    (f := fun index => weights index * contribution alpha beta u v w index)
  unfold publicCombined privateCombined
  rw [add_comm, partition]
  unfold contribution weighted
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 2 <;> apply Finset.sum_congr rfl <;> intro index member <;> ring

/-- The key's public/private query split plus the independently supplied QAP
identity yields the ideal compatible offset relation. Neither successful
proof verification nor an accepted R1CS checker is a premise. -/
theorem qap_compatible (publicIndices : Finset ι) (weights : ι → F)
    (alpha beta gamma delta h z : F) (gammaNonzero : gamma ≠ 0) (deltaNonzero : delta ≠ 0)
    (u v w : ι → F)
    (qap : weighted weights u * weighted weights v - weighted weights w = h * z) :
    delta * ((privateCombined publicIndices weights alpha beta u v w + h * z) / delta) =
      (alpha + weighted weights u) * (beta + weighted weights v) -
        (alpha * beta + gamma * (publicCombined publicIndices weights alpha beta u v w / gamma)) := by
  have partition := combined_partition publicIndices weights alpha beta u v w
  rw [mul_div_cancel₀ _ deltaNonzero]
  rw [mul_div_cancel₀ _ gammaNonzero]
  rw [← qap]
  calc
    _ = publicCombined publicIndices weights alpha beta u v w +
      privateCombined publicIndices weights alpha beta u v w +
      weighted weights u * weighted weights v - weighted weights w -
      publicCombined publicIndices weights alpha beta u v w := by ring
    _ = _ := by rw [partition]; ring

def offsetsOfQap (publicIndices : Finset ι) (weights : ι → F)
    (setup : IdealGroth16.Setup F) (u v w : ι → F) (h z : F)
    (gammaNonzero : setup.gamma ≠ 0)
    (publicQuery : setup.publicIC =
      publicCombined publicIndices weights setup.alpha setup.beta u v w / setup.gamma)
    (qap : weighted weights u * weighted weights v - weighted weights w = h * z) :
    IdealGroth16.WitnessOffsets setup where
  A := setup.alpha + weighted weights u
  B := setup.beta + weighted weights v
  K := (privateCombined publicIndices weights setup.alpha setup.beta u v w + h * z) / setup.delta
  compatible := by
    unfold IdealGroth16.Setup.kappa
    rw [publicQuery]
    exact qap_compatible publicIndices weights setup.alpha setup.beta setup.gamma setup.delta h z
      gammaNonzero setup.delta_ne_zero u v w qap

end LeanCrypto.Proofs.Groth16Setup

#print axioms LeanCrypto.Proofs.Groth16Setup.combined_partition
#print axioms LeanCrypto.Proofs.Groth16Setup.qap_compatible
