import LeanCryptoProofs.BabyJubjub.SignedWindows
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjubWindows
open LeanCrypto.Proofs.BabyJubjubPrimes

/-- The high-place recurrence for the same signed-window magnitude bound. -/
theorem windowBound_high (n : Nat) : windowBound (n+1) = windowBound n + 8 * 32 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      windowBound (n+1+1) = 8+32*windowBound (n+1) := rfl
      _ = 8+32*(windowBound n+8*32^n) := by rw [ih]
      _ = windowBound (n+1)+8*32^(n+1) := by rw [windowBound, pow_succ]; ring

theorem windowValue_append (first second : List Int) :
    windowValue (first ++ second) = windowValue first + 32 ^ first.length * windowValue second := by
  induction first with
  | nil => simp [windowValue]
  | cons digit rest ih =>
    simp only [List.cons_append, windowValue, List.length_cons, pow_succ, ih]
    ring

theorem highPlace_positive (n : Nat) : (0 : Int) < 32 ^ n := pow_pos (by decide) _

theorem valid_prefix_lt_highPlace (digits : List Int) (valid : ValidDigits digits) :
    |windowValue digits| < 32 ^ digits.length := by
  have bound := windowValue_bound digits valid
  have dominates := windowBound_dominance digits.length
  exact lt_of_le_of_lt bound (by exact_mod_cast dominates)

theorem signed_highPlace_magnitude (digit : Int) (n : Nat) (low : 1 ≤ |digit|) :
    (32 : Int)^n ≤ |digit * 32^n| := by
  rw [abs_mul, abs_of_pos (highPlace_positive n)]
  nlinarith [highPlace_positive n]

/-- A previous signed prefix cannot cancel or equal the next nonzero window. -/
theorem prefix_highPlace_separated (digits : List Int) (valid : ValidDigits digits)
    (digit : Int) (low : 1 ≤ |digit|) :
    windowValue digits - digit * 32^digits.length ≠ 0 ∧
      windowValue digits + digit * 32^digits.length ≠ 0 := by
  have small := valid_prefix_lt_highPlace digits valid
  have large := signed_highPlace_magnitude digit digits.length low
  constructor
  · intro zero
    have equal := sub_eq_zero.mp zero
    rw [equal] at small
    exact (not_lt_of_ge large) small
  · intro zero
    have equal : windowValue digits = -(digit*32^digits.length) := eq_neg_of_add_eq_zero_left zero
    rw [equal, abs_neg] at small
    exact (not_lt_of_ge large) small

theorem prefix_highPlace_bounds (digits : List Int) (valid : ValidDigits digits)
    (digit : Int) (high : |digit| ≤ 8) (size : digits.length < 50) :
    |windowValue digits - digit * 32^digits.length| < (subgroupOrder : Int) ∧
      |windowValue digits + digit * 32^digits.length| < (subgroupOrder : Int) := by
  have prefixBound := windowValue_bound digits valid
  have digitBound : |digit * 32^digits.length| ≤ 8 * (32 : Int)^digits.length := by
    rw [abs_mul, abs_of_pos (highPlace_positive _)]
    exact mul_le_mul_of_nonneg_right high (le_of_lt (highPlace_positive _))
  have exactBound : (windowBound digits.length : Int) + 8*32^digits.length =
      (windowBound (digits.length+1) : Int) := by
    rw [windowBound_high, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    rfl
  have maximum : (windowBound (digits.length+1) : Int) < subgroupOrder := by
    exact_mod_cast lt_of_le_of_lt (windowBound_mono (by omega : digits.length+1 ≤ 50)) maximum_window_bound
  constructor
  · exact lt_of_le_of_lt (abs_sub _ _ |>.trans (add_le_add prefixBound digitBound)) (exactBound.symm ▸ maximum)
  · exact lt_of_le_of_lt (abs_add_le _ _ |>.trans (add_le_add prefixBound digitBound)) (exactBound.symm ▸ maximum)

variable {G : Type*} [AddCommGroup G]

theorem small_zsmul_nonzero (point : G) (order : addOrderOf point = subgroupOrder)
    (scalar : Int) (nonzero : scalar ≠ 0) (bound : |scalar| < (subgroupOrder : Int)) :
    scalar • point ≠ 0 := by
  intro zero
  have divides : (addOrderOf point : Int) ∣ scalar := addOrderOf_dvd_iff_zsmul_eq_zero.mpr zero
  rw [order] at divides
  exact nonzero (Int.eq_zero_of_abs_lt_dvd divides bound)

theorem prefix_highPlace_group_separated (point : G) (order : addOrderOf point = subgroupOrder)
    (digits : List Int) (valid : ValidDigits digits) (digit : Int)
    (low : 1 ≤ |digit|) (high : |digit| ≤ 8) (size : digits.length < 50) :
    windowValue digits • point ≠ (digit*32^digits.length) • point ∧
      windowValue digits • point ≠ -((digit*32^digits.length) • point) := by
  have nonzero := prefix_highPlace_separated digits valid digit low
  have bounded := prefix_highPlace_bounds digits valid digit high size
  constructor
  · intro equal
    apply small_zsmul_nonzero point order _ nonzero.1 bounded.1
    rw [sub_zsmul, equal, add_neg_cancel]
  · intro equal
    apply small_zsmul_nonzero point order _ nonzero.2 bounded.2
    rw [add_zsmul, equal, neg_add_cancel]

end LeanCrypto.Proofs.BabyJubjubWindows
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.windowBound_high
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.windowValue_append
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.highPlace_positive
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.valid_prefix_lt_highPlace
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.signed_highPlace_magnitude
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.prefix_highPlace_separated
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.prefix_highPlace_bounds
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.small_zsmul_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.prefix_highPlace_group_separated
