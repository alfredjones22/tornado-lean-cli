import LeanCryptoProofs.BabyJubjub.Primes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjubWindows
open LeanCrypto.Proofs.BabyJubjubPrimes

def windowBound : Nat → Nat
  | 0 => 0
  | n + 1 => 8 + 32 * windowBound n

def windowValue : List Int → Int
  | [] => 0
  | digit :: rest => digit + 32 * windowValue rest

def ValidDigits (digits : List Int) : Prop :=
  ∀ digit ∈ digits, 1 ≤ |digit| ∧ |digit| ≤ 8

theorem windowBound_mono : Monotone windowBound := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [windowBound]
  omega

theorem windowBound_dominance (n : Nat) : windowBound n < 32 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [windowBound, pow_succ]
    have positive : 0 < 32 ^ n := pow_pos (by decide) _
    omega

theorem windowValue_bound (digits : List Int) (valid : ValidDigits digits) :
    |windowValue digits| ≤ (windowBound digits.length : Int) := by
  induction digits with
  | nil => simp [windowValue, windowBound]
  | cons digit rest ih =>
    have hd := (valid digit (by simp)).2
    have hr := ih (fun digit member => valid digit (by simp [member]))
    simp only [windowValue, List.length_cons, windowBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ |digit| + |32 * windowValue rest| := abs_add_le _ _
      _ = |digit| + 32 * |windowValue rest| := by rw [abs_mul]; norm_num
      _ ≤ _ := add_le_add hd (mul_le_mul_of_nonneg_left hr (by decide))

theorem windowValue_nonzero (digit : Int) (rest : List Int)
    (valid : ValidDigits (digit :: rest)) : windowValue (digit :: rest) ≠ 0 := by
  have bounds := valid digit (by simp)
  have signedBounds := abs_le.mp bounds.2
  have nonzero : digit ≠ 0 := by intro zero; simp [zero] at bounds
  intro zero
  simp only [windowValue] at zero
  omega

theorem maximum_window_bound : windowBound 50 < subgroupOrder := by decide +kernel

theorem bounded_window_scalar (digits : List Int) (valid : ValidDigits digits)
    (size : digits.length ≤ 50) : |windowValue digits| < (subgroupOrder : Int) := by
  have bounded := windowValue_bound digits valid
  have lengthBound := windowBound_mono size
  have maximum := maximum_window_bound
  exact lt_of_le_of_lt bounded (by exact_mod_cast lt_of_le_of_lt lengthBound maximum)

def canonicalScalar (scalar : Int) : Nat :=
  (if scalar < 0 then scalar + (subgroupOrder : Int) else scalar).toNat

theorem canonicalScalar_bounds (scalar : Int) (nonzero : scalar ≠ 0)
    (bounded : |scalar| < (subgroupOrder : Int)) :
    0 < canonicalScalar scalar ∧ canonicalScalar scalar < subgroupOrder := by
  have magnitude := abs_lt.mp bounded
  unfold canonicalScalar
  split <;> omega

theorem valid_chunk_scalar (digit : Int) (rest : List Int)
    (valid : ValidDigits (digit :: rest)) (size : (digit :: rest).length ≤ 50) :
    0 < canonicalScalar (windowValue (digit :: rest)) ∧
      canonicalScalar (windowValue (digit :: rest)) < subgroupOrder :=
  canonicalScalar_bounds _ (windowValue_nonzero digit rest valid)
    (bounded_window_scalar _ valid size)

end LeanCrypto.Proofs.BabyJubjubWindows
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.windowBound_mono
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.windowBound_dominance
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.windowValue_bound
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.windowValue_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.maximum_window_bound
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.bounded_window_scalar
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.canonicalScalar_bounds
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.valid_chunk_scalar
