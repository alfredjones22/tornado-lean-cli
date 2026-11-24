import TornadoProofs.Witness.ConcatBits
import TornadoProofs.Witness.ReferenceWeights

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.WitnessVM
open TornadoProofs.Witness.PedersenReference
open LeanCrypto.Proofs.BabyJubjubWindows

theorem low_nibble_bits (value : Nat) :
    value%2 + 2*(value/2%2) + 4*(value/4%2) + 8*(value/8%2) = value%16 := by omega

theorem high_nibble_bits (value : Nat) (bound : value<256) :
    value/16%2 + 2*(value/32%2) + 4*(value/64%2) + 8*(value/128%2) = value/16 := by omega

theorem native_bit_byte_window (bytes : ByteArray) (start index bit : Nat)
    (within : start+index/2 < bytes.size) (small : bit<4) :
    bitValue (nativeLittleEndian bytes) (8*start+4*index+bit) =
      bitValue (bytes.get! (start+index/2)).toNat (4*(index%2)+bit) := by
  have parity := Nat.mod_lt index (by decide : 0<2)
  have offset : 4*(index%2)+bit<8 := by omega
  have position : 8*start+4*index+bit=8*(start+index/2)+(4*(index%2)+bit) := by omega
  rw [position,nativeLittleEndian_bit bytes (start+index/2) _ within offset]

theorem digitAt_native_byte (bytes : ByteArray) (start index : Nat)
    (within : start+index/2 < bytes.size) :
    digitAt (bitValue (nativeLittleEndian bytes)) (8*start) index =
      nativeNibble (if index%2=0 then (bytes.get! (start+index/2)).toNat%16
        else (bytes.get! (start+index/2)).toNat/16) := by
  have bit0 := native_bit_byte_window bytes start index 0 within (by decide)
  have bit1 := native_bit_byte_window bytes start index 1 within (by decide)
  have bit2 := native_bit_byte_window bytes start index 2 within (by decide)
  have bit3 := native_bit_byte_window bytes start index 3 within (by decide)
  simp only [Nat.add_zero] at bit0
  unfold digitAt PedersenWindows.selectorIndex
  rw [bit0,bit1,bit2,bit3]
  have parity : index%2=0 ∨ index%2=1 := by have bound := Nat.mod_lt index (by decide : 0<2); omega
  rcases parity with even | odd
  · simp only [even,↓reduceIte,Nat.mul_zero,Nat.zero_add,bitValue,Nat.reducePow,Nat.div_one]
    rw [low_nibble_bits]
  · simp only [odd,show ¬1=0 from by decide,↓reduceIte,Nat.mul_one,bitValue,Nat.reduceAdd,Nat.reducePow]
    rw [high_nibble_bits _ (bytes.get! (start+index/2)).toNat_lt]

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.low_nibble_bits
#print axioms TornadoProofs.Witness.Source.high_nibble_bits
#print axioms TornadoProofs.Witness.Source.native_bit_byte_window
#print axioms TornadoProofs.Witness.Source.digitAt_native_byte
