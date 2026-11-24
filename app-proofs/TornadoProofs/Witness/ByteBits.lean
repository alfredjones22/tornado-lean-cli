import TornadoProofs.Witness.PrefixCanonical
import Init.Data.Nat.Mod

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.WitnessVM

theorem byteSum_next (bytes : ByteArray) (width : Nat) :
    byteSum bytes (width+1) =
      byteSum bytes width + (bytes.get! width).toNat * 2^(8*width) := by
  simp only [byteSum, List.range_succ, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton]

theorem byteSum_truncate (bytes : ByteArray) (width cutoff : Nat)
    (within : cutoff ≤ width) :
    byteSum bytes width % 2^(8*cutoff) = byteSum bytes cutoff := by
  induction width with
  | zero =>
    have h : cutoff = 0 := by omega
    subst cutoff
    simp [byteSum]
  | succ width ih =>
    by_cases same : cutoff = width+1
    · subst cutoff
      exact Nat.mod_eq_of_lt (byteSum_bound bytes (width+1))
    · have earlier : cutoff ≤ width := by omega
      have divides : 2^(8*cutoff) ∣ (bytes.get! width).toNat * 2^(8*width) :=
        dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (Nat.mul_le_mul_left 8 earlier)) _
      rw [byteSum_next, Nat.add_mod, Nat.mod_eq_zero_of_dvd divides, Nat.add_zero,
        ih earlier, Nat.mod_eq_of_lt (byteSum_bound bytes cutoff)]

theorem nativeLittleEndian_byte (bytes : ByteArray) (index : Nat)
    (within : index < bytes.size) :
    nativeLittleEndian bytes / 2^(8*index) % 256 = (bytes.get! index).toNat := by
  rw [nativeLittleEndian_sum]
  have power : 2^(8*(index+1)) = 2^(8*index)*256 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  rw [← Nat.mod_mul_right_div_self, ← power,
    byteSum_truncate bytes bytes.size (index+1) (by omega), byteSum_next,
    Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (byteSum_bound bytes index), Nat.zero_add]

theorem lowByte_bit (value offset : Nat) (small : offset < 8) :
    value % 256 / 2^offset % 2 = value / 2^offset % 2 := by
  have divides : 2^offset * 2 ∣ 256 := by
    have bounded : offset+1 ≤ 8 := by omega
    simpa only [Nat.pow_succ] using Nat.pow_dvd_pow 2 bounded
  rw [← Nat.mod_mul_right_div_self (value % 256) (2^offset) 2,
    Nat.mod_mod_of_dvd value divides, Nat.mod_mul_right_div_self]

theorem nativeLittleEndian_bit (bytes : ByteArray) (index offset : Nat)
    (within : index < bytes.size) (small : offset < 8) :
    bitValue (nativeLittleEndian bytes) (8*index+offset) =
      bitValue (bytes.get! index).toNat offset := by
  simp only [bitValue, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  rw [← lowByte_bit _ offset small, nativeLittleEndian_byte bytes index within]

theorem nativeLittleEndian_bit_at (bytes : ByteArray) (position : Nat)
    (within : position < 8*bytes.size) :
    bitValue (nativeLittleEndian bytes) position =
      ((bytes.get! (position/8)).toNat / 2^(position%8))%2 := by
  have bounded : position/8 < bytes.size := by omega
  have offset : position%8 < 8 := Nat.mod_lt _ (by decide)
  have split : 8*(position/8)+position%8 = position := by omega
  simpa only [split, bitValue] using nativeLittleEndian_bit bytes (position/8)
    (position%8) bounded offset

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.byteSum_next
#print axioms TornadoProofs.Witness.Source.byteSum_truncate
#print axioms TornadoProofs.Witness.Source.nativeLittleEndian_byte
#print axioms TornadoProofs.Witness.Source.lowByte_bit
#print axioms TornadoProofs.Witness.Source.nativeLittleEndian_bit
#print axioms TornadoProofs.Witness.Source.nativeLittleEndian_bit_at
