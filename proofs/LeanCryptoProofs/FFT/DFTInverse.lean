import LeanCryptoProofs.FFT.DFT
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

theorem geometric_product (value : Fr) (length : Nat) :
    (∑ index ∈ Finset.range length, value ^ index) * (value - 1) = value ^ length - 1 := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
    ring

theorem character_sum (length exponent : Nat) (root : Fr) (primitive : IsPrimitiveRoot root length) :
    (∑ index ∈ Finset.range length, root ^ (index * exponent)) =
      if length ∣ exponent then (length : Fr) else 0 := by
  by_cases divides : length ∣ exponent
  · have power := (primitive.pow_eq_one_iff_dvd exponent).2 divides
    rw [if_pos divides]
    simp only [Nat.mul_comm _ exponent, pow_mul, power, one_pow]
    simp
  · rw [if_neg divides]
    have different : root ^ exponent ≠ 1 := fun equal => divides (primitive.dvd_of_pow_eq_one exponent equal)
    have power : (root ^ exponent) ^ length = 1 := by
      rw [← pow_mul, Nat.mul_comm exponent length, pow_mul, primitive.pow_eq_one, one_pow]
    have product := geometric_product (root ^ exponent) length
    rw [power, sub_self] at product
    have zero := (mul_eq_zero.mp product).resolve_right (sub_ne_zero.mpr different)
    simpa only [← pow_mul, Nat.mul_comm] using zero

theorem delta_divides (length left right : Nat) (positive : 0 < length)
    (leftBound : left < length) (rightBound : right < length) :
    length ∣ right + length - left ↔ left = right := by
  constructor
  · rintro ⟨multiplier, equation⟩
    have numberPositive : 0 < right + length - left := by omega
    have numberBound : right + length - left < length * 2 := by omega
    have multiplierPositive : 0 < multiplier := by
      have productPositive : 0 < length * multiplier := by rw [← equation]; exact numberPositive
      apply Nat.pos_of_ne_zero
      intro zero
      rw [zero, mul_zero] at productPositive
      omega
    have multiplierBound : multiplier < 2 :=
      Nat.lt_of_mul_lt_mul_left (by rw [← equation]; exact numberBound)
    have multiplierOne : multiplier = 1 := by omega
    rw [multiplierOne, mul_one] at equation
    omega
  · intro equal
    subst right
    simp

theorem inverse_root_power (length index : Nat) (root : Fr)
    (primitive : IsPrimitiveRoot root length) (positive : 0 < length) (bounded : index < length) :
    root⁻¹ ^ index = root ^ (length - index) := by
  have nonzero : root ≠ 0 := (primitive.isUnit (Nat.ne_of_gt positive)).ne_zero
  apply mul_left_cancel₀ (pow_ne_zero index nonzero)
  calc
    root ^ index * root⁻¹ ^ index = 1 := by rw [← mul_pow, mul_inv_cancel₀ nonzero, one_pow]
    _ = root ^ index * root ^ (length - index) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt bounded), primitive.pow_eq_one]

theorem inverseDft_dft (length : Nat) (root : Fr) (input : Nat → Fr) (index : Nat)
    (positive : 0 < length) (indexBound : index < length)
    (primitive : IsPrimitiveRoot root length) (sizeNonzero : (length : Fr) ≠ 0) :
    inverseDft length root (dft length root input) index = input index := by
  have powers (frequency coefficient : Nat) :
      root ^ (frequency * coefficient) * root⁻¹ ^ (index * frequency) =
        root ^ (frequency * (coefficient + length - index)) := by
    rw [pow_mul root⁻¹, inverse_root_power length index root primitive positive indexBound, ← pow_mul, ← pow_add]
    congr 1
    rw [Nat.add_sub_assoc (Nat.le_of_lt indexBound)]
    ring
  have inner (coefficient : Nat) (coefficientBound : coefficient < length) :
      (∑ frequency ∈ Finset.range length,
        (input coefficient * root ^ (frequency * coefficient)) * root⁻¹ ^ (index * frequency)) =
        input coefficient * (if index = coefficient then (length : Fr) else 0) := by
    calc
      _ = input coefficient * ∑ frequency ∈ Finset.range length,
          root ^ (frequency * (coefficient + length - index)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro frequency member
        rw [mul_assoc, powers]
      _ = _ := by
        rw [character_sum length _ root primitive]
        simp only [delta_divides length index coefficient positive indexBound coefficientBound]
  unfold inverseDft dft
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = (length : Fr)⁻¹ * ∑ coefficient ∈ Finset.range length,
        input coefficient * (if index = coefficient then (length : Fr) else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro coefficient member
      exact inner coefficient (Finset.mem_range.mp member)
    _ = (length : Fr)⁻¹ * (input index * (length : Fr)) := by
      congr 1
      simp [Finset.mem_range.mpr indexBound]
    _ = input index := by
      rw [show (length : Fr)⁻¹ * (input index * (length : Fr)) =
        input index * ((length : Fr)⁻¹ * (length : Fr)) by ring,
        inv_mul_cancel₀ sizeNonzero, mul_one]

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.geometric_product
#print axioms LeanCrypto.Proofs.FFT.character_sum
#print axioms LeanCrypto.Proofs.FFT.delta_divides
#print axioms LeanCrypto.Proofs.FFT.inverse_root_power
#print axioms LeanCrypto.Proofs.FFT.inverseDft_dft
