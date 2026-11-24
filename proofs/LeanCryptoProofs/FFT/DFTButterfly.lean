import LeanCryptoProofs.FFT.DFT
import LeanCryptoProofs.FFT.BitReverse
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

theorem sum_range_double {R : Type} [AddCommMonoid R] (f : Nat → R) (length : Nat) :
    (∑ index ∈ Finset.range (2 * length), f index) =
      ∑ index ∈ Finset.range length, (f (2 * index) + f (2 * index + 1)) := by
  induction length with
  | zero => simp
  | succ length ih =>
    have expansion : 2 * (length + 1) = 2 * length + 1 + 1 := by omega
    rw [expansion, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [add_assoc]

theorem dft_even_odd (half : Nat) (root : Fr) (input : Nat → Fr) (index : Nat) :
    dft (2 * half) root input index =
      dft half (root ^ 2) (fun i => input (2 * i)) index +
      root ^ index * dft half (root ^ 2) (fun i => input (2 * i + 1)) index := by
  unfold dft
  rw [sum_range_double, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i member
    rw [← pow_mul]
    congr 1
    congr 1
    ring
  · apply Finset.sum_congr rfl
    intro i member
    have exponent : index * (2 * i + 1) = 2 * (index * i) + index := by ring
    rw [exponent, pow_add, ← pow_mul]
    ring

theorem dft_index_period (length period index : Nat) (root : Fr) (input : Nat → Fr)
    (periodic : root ^ period = 1) :
    dft length root input (index + period) = dft length root input index := by
  unfold dft
  apply Finset.sum_congr rfl
  intro i member
  simp only [Nat.add_mul, pow_add, pow_mul, periodic, one_pow, mul_one]

theorem dft_butterfly_upper (half : Nat) (root : Fr) (input : Nat → Fr) (index : Nat)
    (halfRoot : root ^ half = -1) :
    dft (2 * half) root input (index + half) =
      dft half (root ^ 2) (fun i => input (2 * i)) index -
      root ^ index * dft half (root ^ 2) (fun i => input (2 * i + 1)) index := by
  have period : (root ^ 2) ^ half = 1 := by
    rw [← pow_mul, Nat.mul_comm 2 half, pow_mul, halfRoot]
    ring
  rw [dft_even_odd, dft_index_period _ _ _ _ _ period, dft_index_period _ _ _ _ _ period,
    pow_add, halfRoot]
  ring

def stageValue (input : Nat → Fr) (root : Fr) (total stage group index : Nat) : Fr :=
  dft (2 ^ stage) (root ^ (2 ^ (total - stage)))
    (fun coefficient => input (reverseNat (total - stage) group + coefficient * 2 ^ (total - stage))) index

theorem stageValue_left (input : Nat → Fr) (root : Fr) (total stage group index : Nat)
    (within : stage < total) :
    stageValue input root total (stage + 1) group index =
      stageValue input root total stage (2 * group) index +
      stageValue input root total stage (2 * group + 1) index *
        root ^ (index * 2 ^ (total - (stage + 1))) := by
  have difference : total - stage = total - (stage + 1) + 1 := by omega
  unfold stageValue
  rw [pow_succ', dft_even_odd]
  have roots : (root ^ (2 ^ (total - (stage + 1)))) ^ 2 = root ^ (2 ^ (total - stage)) := by
    rw [difference, ← pow_mul, ← pow_succ]
  rw [roots, difference, reverseNat_even, reverseNat_odd]
  have evenInput : (fun i => input (reverseNat (total - (stage + 1)) group +
      2 * i * 2 ^ (total - (stage + 1)))) =
      (fun i => input (reverseNat (total - (stage + 1)) group +
        i * 2 ^ (total - (stage + 1) + 1))) := by
    funext i
    congr 1
    rw [pow_succ]
    ring
  have oddInput : (fun i => input (reverseNat (total - (stage + 1)) group +
      (2 * i + 1) * 2 ^ (total - (stage + 1)))) =
      (fun i => input (reverseNat (total - (stage + 1)) group + 2 ^ (total - (stage + 1)) +
        i * 2 ^ (total - (stage + 1) + 1))) := by
    funext i
    congr 1
    rw [pow_succ]
    ring
  rw [evenInput, oddInput, ← pow_mul]
  ring

theorem stageValue_upper (input : Nat → Fr) (root : Fr) (total stage group index : Nat)
    (within : stage < total) (halfRoot : root ^ (2 ^ (total - 1)) = -1) :
    stageValue input root total (stage + 1) group (index + 2 ^ stage) =
      stageValue input root total stage (2 * group) index -
      stageValue input root total stage (2 * group + 1) index *
        root ^ (index * 2 ^ (total - (stage + 1))) := by
  have difference : total - stage = total - (stage + 1) + 1 := by omega
  have liftedHalf : (root ^ (2 ^ (total - (stage + 1)))) ^ (2 ^ stage) = -1 := by
    rw [← pow_mul, ← pow_add]
    have exponent : total - (stage + 1) + stage = total - 1 := by omega
    rw [exponent]
    exact halfRoot
  unfold stageValue
  rw [pow_succ', dft_butterfly_upper _ _ _ _ liftedHalf]
  have roots : (root ^ (2 ^ (total - (stage + 1)))) ^ 2 = root ^ (2 ^ (total - stage)) := by
    rw [difference, ← pow_mul, ← pow_succ]
  rw [roots, difference, reverseNat_even, reverseNat_odd]
  have evenInput : (fun i => input (reverseNat (total - (stage + 1)) group +
      2 * i * 2 ^ (total - (stage + 1)))) =
      (fun i => input (reverseNat (total - (stage + 1)) group +
        i * 2 ^ (total - (stage + 1) + 1))) := by
    funext i
    congr 1
    rw [pow_succ]
    ring
  have oddInput : (fun i => input (reverseNat (total - (stage + 1)) group +
      (2 * i + 1) * 2 ^ (total - (stage + 1)))) =
      (fun i => input (reverseNat (total - (stage + 1)) group + 2 ^ (total - (stage + 1)) +
        i * 2 ^ (total - (stage + 1) + 1))) := by
    funext i
    congr 1
    rw [pow_succ]
    ring
  rw [evenInput, oddInput, ← pow_mul]
  ring


theorem stageValue_initial (input : Nat → Fr) (root : Fr) (total group : Nat) :
    stageValue input root total 0 group 0 = input (reverseNat total group) := by
  simp [stageValue, dft]

theorem stageValue_final (input : Nat → Fr) (root : Fr) (total index : Nat) :
    stageValue input root total total 0 index = dft (2 ^ total) root input index := by
  simp [stageValue, reverseNat_zero]

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.sum_range_double
#print axioms LeanCrypto.Proofs.FFT.dft_even_odd
#print axioms LeanCrypto.Proofs.FFT.dft_index_period
#print axioms LeanCrypto.Proofs.FFT.dft_butterfly_upper
#print axioms LeanCrypto.Proofs.FFT.stageValue_left

#print axioms LeanCrypto.Proofs.FFT.stageValue_upper
#print axioms LeanCrypto.Proofs.FFT.stageValue_initial
#print axioms LeanCrypto.Proofs.FFT.stageValue_final
