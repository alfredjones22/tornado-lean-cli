import TornadoProofs.Witness.NativePath
import Tornado.Protocol.TornadoWitness

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.TornadoWitness
open TornadoProofs.Witness.Execution

def prefixHeader (input : WithdrawalInput) : Array Nat :=
  #[1,input.proof.root,input.note.nullifierHash,input.recipient,input.relayer,input.fee,input.refund,
    input.note.nullifier,input.note.secret]

theorem inputPrefix_header (input : WithdrawalInput) (index : Nat) (bound : index<9) :
    (inputPrefix input)[index]! = (prefixHeader input)[index]! := by
  change (((prefixHeader input++input.proof.siblings)++input.proof.pathIndices)[index]!)=_
  have headerBound : index<(prefixHeader input).size := bound
  have middleBound : index<(prefixHeader input++input.proof.siblings).size := by simp only [Array.size_append]; omega
  have fullBound : index<((prefixHeader input++input.proof.siblings)++input.proof.pathIndices).size := by
    simp only [Array.size_append]; omega
  rw [getElem!_pos _ index fullBound,Array.getElem_append_left middleBound,
    Array.getElem_append_left headerBound,getElem!_pos _ index headerBound]

theorem inputPrefix_sibling (input : WithdrawalInput) (siblings : input.proof.siblings.size=20)
    (index : Nat) (bound : index<20) : (inputPrefix input)[9+index]! = input.proof.siblings[index]! := by
  change (((prefixHeader input++input.proof.siblings)++input.proof.pathIndices)[9+index]!)=_
  have headerSize : (prefixHeader input).size=9 := rfl
  have siblingBound : index < input.proof.siblings.size := by simpa only [siblings] using bound
  have middleBound : 9+index<(prefixHeader input++input.proof.siblings).size := by simp only [Array.size_append,headerSize,siblings]; omega
  have fullBound : 9+index<((prefixHeader input++input.proof.siblings)++input.proof.pathIndices).size := by
    simp only [Array.size_append,headerSize,siblings]; omega
  rw [getElem!_pos _ (9+index) fullBound,Array.getElem_append_left middleBound,
    Array.getElem_append_right (by simp only [headerSize]; omega)]
  simp only [headerSize,Nat.add_sub_cancel_left,getElem!_pos input.proof.siblings index siblingBound]

theorem inputPrefix_direction (input : WithdrawalInput) (siblings : input.proof.siblings.size=20)
    (directions : input.proof.pathIndices.size=20) (index : Nat) (bound : index<20) :
    (inputPrefix input)[29+index]! = input.proof.pathIndices[index]! := by
  change (((prefixHeader input++input.proof.siblings)++input.proof.pathIndices)[29+index]!)=_
  have headerSize : (prefixHeader input).size=9 := rfl
  have directionBound : index < input.proof.pathIndices.size := by simpa only [directions] using bound
  have fullBound : 29+index<((prefixHeader input++input.proof.siblings)++input.proof.pathIndices).size := by
    simp only [Array.size_append,headerSize,siblings,directions]; omega
  rw [getElem!_pos _ (29+index) fullBound,Array.getElem_append_right (by
    simp only [Array.size_append,headerSize,siblings]; omega)]
  simp only [Array.size_append,headerSize,siblings,Nat.reduceAdd,Nat.add_sub_cancel_left,
    getElem!_pos input.proof.pathIndices index directionBound]

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.inputPrefix_header
#print axioms TornadoProofs.Witness.Source.inputPrefix_sibling
#print axioms TornadoProofs.Witness.Source.inputPrefix_direction
