import LeanCryptoProofs.BabyJubjub.WindowSeparation

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjubWindows
open LeanCrypto.Proofs.BabyJubjubPrimes

theorem maximum_double_window_bound : 2 * windowBound 50 < subgroupOrder := by decide +kernel

theorem maximum_table_bound : 16 * 32 ^ 49 < subgroupOrder := by decide +kernel

theorem small_table_bound (coefficient : Int) (bounded : |coefficient| ≤ 16) (n : Nat) (size : n < 50) :
    |coefficient * 32^n| < (subgroupOrder : Int) := by
  have power : (32 : Int)^n ≤ 32^49 := pow_le_pow_right₀ (by decide) (by omega)
  calc
    _ = |coefficient| * 32^n := by rw [abs_mul, abs_of_pos (highPlace_positive n)]
    _ ≤ 16*32^n := mul_le_mul_of_nonneg_right bounded (le_of_lt (highPlace_positive n))
    _ ≤ 16*32^49 := mul_le_mul_of_nonneg_left power (by decide)
    _ < _ := by exact_mod_cast maximum_table_bound

theorem double_prefix_bound (digits : List Int) (valid : ValidDigits digits) (size : digits.length ≤ 50) :
    |2 * windowValue digits| < (subgroupOrder : Int) := by
  have bounded := windowValue_bound digits valid
  have lengthBound := windowBound_mono size
  have maximum := maximum_double_window_bound
  rw [abs_mul]
  rw [show |(2 : Int)| = 2 from rfl]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left bounded (by decide)) (by exact_mod_cast (lt_of_le_of_lt
    (Nat.mul_le_mul_left 2 lengthBound) maximum))

variable {G : Type*} [AddCommGroup G]

theorem canonicalScalar_group (point : G) (order : addOrderOf point = subgroupOrder)
    (scalar : Int) (bounded : |scalar| < (subgroupOrder : Int)) :
    canonicalScalar scalar • point = scalar • point := by
  have annihilates : subgroupOrder • point = 0 := order ▸ addOrderOf_nsmul_eq_zero point
  have magnitude := abs_lt.mp bounded
  unfold canonicalScalar
  split
  · rename_i negative
    have nonnegative : 0 ≤ scalar + (subgroupOrder : Int) := by omega
    rw [← natCast_zsmul, Int.toNat_of_nonneg nonnegative, add_zsmul, natCast_zsmul, annihilates, add_zero]
  · rename_i nonnegative
    rw [← natCast_zsmul, Int.toNat_of_nonneg (by omega)]

theorem valid_prefix_group_nonzero (point : G) (order : addOrderOf point = subgroupOrder)
    (digit : Int) (rest : List Int) (valid : ValidDigits (digit::rest)) (size : (digit::rest).length ≤ 50) :
    windowValue (digit::rest) • point ≠ 0 :=
  small_zsmul_nonzero point order _ (windowValue_nonzero digit rest valid)
    (bounded_window_scalar _ valid size)

theorem valid_prefix_group_double_nonzero (point : G) (order : addOrderOf point = subgroupOrder)
    (digit : Int) (rest : List Int) (valid : ValidDigits (digit::rest)) (size : (digit::rest).length ≤ 50) :
    (2 : Int) • (windowValue (digit::rest) • point) ≠ 0 := by
  rw [← mul_smul]
  apply small_zsmul_nonzero point order _ _ (double_prefix_bound _ valid size)
  have value := windowValue_nonzero digit rest valid
  exact mul_ne_zero (by decide) value

theorem table_group_nonzero (point : G) (order : addOrderOf point = subgroupOrder)
    (coefficient : Int) (nonzero : coefficient ≠ 0) (bounded : |coefficient| ≤ 16) (n : Nat) (size : n < 50) :
    (coefficient*32^n) • point ≠ 0 :=
  small_zsmul_nonzero point order _ (mul_ne_zero nonzero (ne_of_gt (highPlace_positive n)))
    (small_table_bound coefficient bounded n size)

theorem table_group_separated (point : G) (order : addOrderOf point = subgroupOrder)
    (first second : Int) (firstLow : 1 ≤ first) (firstHigh : first ≤ 8)
    (secondLow : 1 ≤ second) (secondHigh : second ≤ 8) (different : first ≠ second)
    (n : Nat) (size : n < 50) :
    (first*32^n) • point ≠ (second*32^n) • point ∧
      (first*32^n) • point ≠ -((second*32^n) • point) := by
  constructor
  · intro equal
    apply table_group_nonzero point order (first-second) (sub_ne_zero.mpr different) (abs_le.mpr ⟨by omega, by omega⟩) n size
    rw [sub_mul, sub_zsmul, equal, add_neg_cancel]
  · intro equal
    apply table_group_nonzero point order (first+second) (by omega) (abs_le.mpr ⟨by omega, by omega⟩) n size
    rw [add_mul, add_zsmul, equal, neg_add_cancel]

end LeanCrypto.Proofs.BabyJubjubWindows
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.maximum_double_window_bound
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.maximum_table_bound
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.small_table_bound
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.double_prefix_bound
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.canonicalScalar_group
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.valid_prefix_group_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.valid_prefix_group_double_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.table_group_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.table_group_separated
