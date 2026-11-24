import LeanCrypto.Hex
import LeanCrypto.FixedBytes

/-! Fixed-width hexadecimal word arithmetic. The two right-recursive
functions are proof references; runtime serializers retain their established
implementations. No field reduction or truncation is used in the inverse. -/
namespace LeanCrypto.Hex

def wordDigits : Nat → Nat → List Char
  | 0, _ => []
  | width + 1, value => wordDigits width (value / 16) ++ [digits[value % 16]!]

private def wordBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => wordBytes width (value / 256) ++ [UInt8.ofNat (value % 256)]

theorem wordDigits_positional (width value : Nat) :
    wordDigits width value = (List.range width).map (fun index =>
      digits[(value / 16 ^ (width - 1 - index)) % 16]!) := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    rw [wordDigits, ih, List.range_succ, List.map_append]
    simp only [List.map_singleton, Nat.add_sub_cancel, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    congr 1
    apply List.map_congr_left
    intro index member
    have bound : index < width := List.mem_range.mp member
    have exponent : width - index = (width - 1 - index) + 1 := by omega
    rw [Nat.div_div_eq_div_mul, exponent, Nat.pow_succ]
    simp only [Nat.mul_comm]

theorem wordBytes_length (width value : Nat) : (wordBytes width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [wordBytes, ih]

theorem decodeList_append_byte (source : List UInt8) (byte : UInt8) :
    LeanCrypto.FixedBytes.decodeList (source ++ [byte]) =
      LeanCrypto.FixedBytes.decodeList source * 256 + byte.toNat := by
  have fold : ∀ bytes : List UInt8,
      bytes.foldl (fun value byte => value * 256 + byte.toNat) 0 =
        LeanCrypto.FixedBytes.decodeList bytes := by
    intro bytes
    simpa using LeanCrypto.FixedBytes.foldl_decodeList bytes 0
  rw [← fold (source ++ [byte]), List.foldl_append, List.foldl_cons, List.foldl_nil, fold source]

theorem wordBytes_inverse (width value : Nat) (bound : value < 256 ^ width) :
    LeanCrypto.FixedBytes.decodeList (wordBytes width value) = value := by
  induction width generalizing value with
  | zero =>
    have zero : value = 0 := by simpa using bound
    subst value
    rfl
  | succ width ih =>
    have quotient : value / 256 < 256 ^ width := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
      simpa only [Nat.pow_succ] using bound
    rw [wordBytes, decodeList_append_byte, ih _ quotient,
      UInt8.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide : 0 < 256))]
    exact Nat.div_add_mod' value 256

theorem wordBytes_eq_fixed (width value : Nat) (bound : value < 256 ^ width) :
    wordBytes width value = LeanCrypto.FixedBytes.encodeList width value := by
  have inverse := LeanCrypto.FixedBytes.encodeList_decodeList (wordBytes width value)
  rw [wordBytes_length, wordBytes_inverse width value bound] at inverse
  exact inverse.symm

theorem wordDigits_pairs (width value : Nat) :
    wordDigits (2 * width) value = encodeList (wordBytes width value) := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    rw [show 2 * (width + 1) = (2 * width + 1) + 1 by omega, wordDigits, wordDigits]
    rw [Nat.div_div_eq_div_mul, show 16 * 16 = 256 by decide, ih]
    rw [wordBytes]
    simp only [encodeList, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have bounded : value % 256 < UInt8.size := Nat.mod_lt _ (by decide)
    simp only [byteChars, UInt8.toNat_ofNat_of_lt' bounded]
    have high : value % 256 / 16 = value / 16 % 16 := Nat.mod_mul_right_div_self value 16 16
    have low : value % 256 % 16 = value % 16 := by omega
    rw [high, low]
    simp only [List.append_assoc, List.singleton_append]

theorem wordDigits_fixed_bytes (width value : Nat) (bound : value < 256 ^ width) :
    wordDigits (2 * width) value = encodeList (LeanCrypto.FixedBytes.encodeList width value) := by
  rw [wordDigits_pairs, wordBytes_eq_fixed width value bound]

end LeanCrypto.Hex

#print axioms LeanCrypto.Hex.wordDigits_positional
#print axioms LeanCrypto.Hex.wordBytes_length
#print axioms LeanCrypto.Hex.decodeList_append_byte
#print axioms LeanCrypto.Hex.wordBytes_inverse
#print axioms LeanCrypto.Hex.wordBytes_eq_fixed
#print axioms LeanCrypto.Hex.wordDigits_pairs
#print axioms LeanCrypto.Hex.wordDigits_fixed_bytes
