import TornadoProofs.Witness.WindowBuilder
import TornadoProofs.Witness.OperationFacts
import TornadoProofs.Witness.PointNegation

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr

def BitMeaning (values : Array Nat) (reference bit : Nat) : Prop := values[reference]! = bit

def muxIDs (b0 b1 b2 : Nat) (table : Array PointRef) : Array Nat :=
  #[b0,b1,b2] ++ table.map Prod.fst ++ table.map Prod.snd

theorem muxInputs_bits (values : Array Nat) (b0 b1 b2 : Nat) (table : Array PointRef) :
    ((muxIDs b0 b1 b2 table).map (values[·]!))[0]! =values[b0]! ∧
    ((muxIDs b0 b1 b2 table).map (values[·]!))[1]! =values[b1]! ∧
    ((muxIDs b0 b1 b2 table).map (values[·]!))[2]! =values[b2]! := by
  simp [muxIDs,getElem!_def,Array.getElem?_append]

theorem muxInputs_coordinates (values : Array Nat) (b0 b1 b2 : Nat) (table : Array PointRef)
    (width : table.size=8) (index : Nat) (bound : index<8) :
    ((muxIDs b0 b1 b2 table).map (values[·]!))[3+index]! =values[table[index]!.1]! ∧
    ((muxIDs b0 b1 b2 table).map (values[·]!))[11+index]! =values[table[index]!.2]! := by
  simp [muxIDs,width,getElem!_def,Array.getElem?_append,bound,
    show ¬11+index<3 from by omega,show ¬11+index-3<8 from by omega,
    show 11+index-3-8=index from by omega]

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.muxInputs_bits
#print axioms TornadoProofs.Witness.PedersenReference.muxInputs_coordinates
