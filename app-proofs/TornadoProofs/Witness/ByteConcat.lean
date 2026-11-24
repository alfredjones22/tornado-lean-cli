import TornadoProofs.Witness.PrefixSlots
import Init.Data.ByteArray.Lemmas

set_option autoImplicit false
namespace TornadoProofs.Witness.Source

/-- Bit observation in the original byte stream, low bit first per byte. -/
def byteBit (bytes : ByteArray) (position : Nat) : Nat :=
  (bytes.get! (position/8)).toNat / 2^(position%8) % 2

theorem byteGet_data (bytes : ByteArray) (index : Nat) : bytes.get! index=bytes.data[index]! := by
  cases bytes
  rfl

theorem byteGet_append_left (left right : ByteArray) (index : Nat) (bound : index < left.size) :
    (left++right).get! index=left.get! index := by
  rw [byteGet_data,byteGet_data,ByteArray.data_append]
  have leftBound : index < left.data.size := bound
  have wholeBound : index < (left.data++right.data).size := by simp only [Array.size_append]; omega
  rw [getElem!_pos _ index wholeBound,Array.getElem_append_left leftBound,getElem!_pos left.data index leftBound]

theorem byteGet_append_right (left right : ByteArray) (index : Nat)
    (past : left.size ≤ index) (bound : index < left.size+right.size) :
    (left++right).get! index=right.get! (index-left.size) := by
  rw [byteGet_data,byteGet_data,ByteArray.data_append]
  have wholeBound : index < (left.data++right.data).size := by simpa only [Array.size_append] using bound
  have pastData : left.data.size ≤ index := past
  have rightBound : index-left.size < right.data.size := by change index-left.size < right.size; omega
  rw [getElem!_pos _ index wholeBound,Array.getElem_append_right pastData]
  exact (getElem!_pos right.data (index-left.size) rightBound).symm

theorem concat31_offsets (position : Nat) (past : 248≤position) :
    position/8-31=(position-248)/8 ∧ position%8=(position-248)%8 := by omega

theorem concat31_bit_left (left right : ByteArray) (leftWidth : left.size=31)
    (position : Nat) (bound : position<248) : byteBit (left++right) position=byteBit left position := by
  unfold byteBit
  rw [byteGet_append_left left right (position/8) (by rw [leftWidth]; omega)]

theorem concat31_bit_right (left right : ByteArray) (leftWidth : left.size=31) (rightWidth : right.size=31)
    (position : Nat) (past : 248≤position) (bound : position<496) :
    byteBit (left++right) position=byteBit right (position-248) := by
  unfold byteBit
  rw [byteGet_append_right left right (position/8) (by rw [leftWidth]; omega)
    (by rw [leftWidth,rightWidth]; omega),leftWidth,(concat31_offsets position past).1,(concat31_offsets position past).2]

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.byteGet_data
#print axioms TornadoProofs.Witness.Source.byteGet_append_left
#print axioms TornadoProofs.Witness.Source.byteGet_append_right
#print axioms TornadoProofs.Witness.Source.concat31_offsets
#print axioms TornadoProofs.Witness.Source.concat31_bit_left
#print axioms TornadoProofs.Witness.Source.concat31_bit_right
