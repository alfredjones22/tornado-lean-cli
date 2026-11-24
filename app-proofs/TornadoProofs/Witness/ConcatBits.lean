import TornadoProofs.Witness.OriginalBits
import TornadoProofs.Witness.ByteBits

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.PedersenSchedule
open Tornado.Protocol.TornadoWitness
open TornadoProofs.Witness.Execution

theorem nativeConcat31_bit (left right : ByteArray) (leftWidth : left.size=31) (rightWidth : right.size=31)
    (position : Nat) (bound : position<496) :
    bitValue (nativeLittleEndian (left++right)) position =
      (if position<248 then bitValue (nativeLittleEndian left) position
      else bitValue (nativeLittleEndian right) (position-248)) := by
  rw [nativeLittleEndian_bit_at (left++right) position (by rw [ByteArray.size_append,leftWidth,rightWidth]; omega)]
  change byteBit (left++right) position=_
  by_cases low : position<248
  · simp only [low,↓reduceIte]
    rw [concat31_bit_left left right leftWidth position low]
    exact (nativeLittleEndian_bit_at left position (by rw [leftWidth]; omega)).symm
  · simp only [low,↓reduceIte]
    rw [concat31_bit_right left right leftWidth rightWidth position (by omega) bound]
    exact (nativeLittleEndian_bit_at right (position-248) (by rw [rightWidth]; omega)).symm

theorem referenceOriginalBit_preimage (input : WithdrawalInput) (source : ValidWithdrawal input)
    (position : Nat) (bound : position<496) :
    referenceOriginalBit input position=bitValue (nativeLittleEndian input.note.preimage) position := by
  change (if position<248 then bitValue (nativeLittleEndian input.note.nullifierBytes) position
    else bitValue (nativeLittleEndian input.note.secretBytes) (position-248))=
      bitValue (nativeLittleEndian (input.note.nullifierBytes++input.note.secretBytes)) position
  exact (nativeConcat31_bit input.note.nullifierBytes input.note.secretBytes source.nullifierWidth source.secretWidth position bound).symm

/-- Every original public bit resolver result is the corresponding bit of
exact native bytes used by Pedersen: nullifier31 alone or nullifier31||secret31. -/
theorem originalBit_native_meaning (resolver : Resolver) (input : WithdrawalInput)
    (source : ValidWithdrawal input) (valid : tableValid resolver.nodes=true)
    (commitment : Bool) (position node : Nat) (compiled : originalBit resolver commitment position=.ok node) :
    (sourceValues resolver (inputPrefix input) input.note.commitment)[node]! =
      bitValue (nativeLittleEndian (if commitment then input.note.preimage else input.note.nullifierBytes)) position := by
  obtain ⟨bound,value⟩ := originalBit_prefix_meaning resolver input source valid commitment position node compiled
  cases commitment with
  | false =>
    have low : position<248 := bound
    change (sourceValues resolver (inputPrefix input) input.note.commitment)[node]! = bitValue input.note.nullifier position
    simpa only [referenceOriginalBit,low,↓reduceIte] using value
  | true =>
    exact value.trans (referenceOriginalBit_preimage input source position bound)

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.nativeConcat31_bit
#print axioms TornadoProofs.Witness.Source.referenceOriginalBit_preimage
#print axioms TornadoProofs.Witness.Source.originalBit_native_meaning
