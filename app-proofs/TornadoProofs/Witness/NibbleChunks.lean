import TornadoProofs.Witness.NibbleList

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.WitnessVM
open TornadoProofs.Witness.PedersenReference
open LeanCrypto.Proofs.BabyJubjubWindows

theorem digits_get (bits : Nat → Nat) (offset count index : Nat) (bound : index<count) :
    (digits bits offset count)[index]! = digitAt bits offset index := by
  simp [digits,getElem!_pos,bound]

theorem native_digits_extract (bytes : ByteArray) (start count : Nat) (within : start+count≤bytes.size) :
    digits (bitValue (nativeLittleEndian bytes)) (8*start) (2*count) =
      byteDigits (bytes.extract start (start+count)).data.toList := by
  apply List.ext_getElem
  · rw [digits_length,byteDigits_length,extract_bytes_length bytes start count within]
  · intro index leftBound rightBound
    have bound : index<2*count := by simpa only [digits_length] using leftBound
    have byteBound : index/2<count := by omega
    have sourceBound : start+index/2 < bytes.size := by omega
    have value : (digits (bitValue (nativeLittleEndian bytes)) (8*start) (2*count))[index]! =
        (byteDigits (bytes.extract start (start+count)).data.toList)[index]! := by
      rw [digits_get _ _ _ index bound,digitAt_native_byte bytes start index sourceBound,
        byteDigits_get _ index (by rw [extract_bytes_length bytes start count within]; exact bound),
        extract_bytes_get bytes start count (index/2) within byteBound]
    simpa only [getElem!_pos (digits (bitValue (nativeLittleEndian bytes)) (8*start) (2*count)) index leftBound,
      getElem!_pos (byteDigits (bytes.extract start (start+count)).data.toList) index rightBound] using value

theorem native_digits_extract_range (bytes : ByteArray) (start stop : Nat)
    (ordered : start≤stop) (within : stop≤bytes.size) :
    digits (bitValue (nativeLittleEndian bytes)) (8*start) (2*(stop-start)) =
      byteDigits (bytes.extract start stop).data.toList := by
  have sum : start+(stop-start)=stop := by omega
  simpa only [sum] using native_digits_extract bytes start (stop-start) (by omega)

theorem note31_chunk_digits (bytes : ByteArray) (width : bytes.size=31) :
    digits (bitValue (nativeLittleEndian bytes)) 0 50=byteDigits (bytes.extract 0 25).data.toList ∧
    digits (bitValue (nativeLittleEndian bytes)) 200 12=byteDigits (bytes.extract 25 31).data.toList := by
  exact ⟨native_digits_extract bytes 0 25 (by omega),
    native_digits_extract bytes 25 6 (by omega)⟩

theorem note62_chunk_digits (bytes : ByteArray) (width : bytes.size=62) :
    digits (bitValue (nativeLittleEndian bytes)) 0 50=byteDigits (bytes.extract 0 25).data.toList ∧
    digits (bitValue (nativeLittleEndian bytes)) 200 50=byteDigits (bytes.extract 25 50).data.toList ∧
    digits (bitValue (nativeLittleEndian bytes)) 400 24=byteDigits (bytes.extract 50 62).data.toList := by
  exact ⟨native_digits_extract bytes 0 25 (by omega),
    native_digits_extract bytes 25 25 (by omega),
    native_digits_extract bytes 50 12 (by omega)⟩

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.digits_get
#print axioms TornadoProofs.Witness.Source.native_digits_extract
#print axioms TornadoProofs.Witness.Source.native_digits_extract_range
#print axioms TornadoProofs.Witness.Source.note31_chunk_digits
#print axioms TornadoProofs.Witness.Source.note62_chunk_digits
