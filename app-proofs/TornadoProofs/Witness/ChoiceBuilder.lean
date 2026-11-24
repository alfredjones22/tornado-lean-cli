import TornadoProofs.Witness.MuxBuilder

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr

theorem choose_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (commitment : Bool)
    (b0 b1 b2 s0 s1 s2 : Nat) (table : Array PointRef) (base : Point)
    (first : BitMeaning values b0 s0) (second : BitMeaning values b1 s1) (third : BitMeaning values b2 s2)
    (bit0 : s0 < 2) (bit1 : s1 < 2) (bit2 : s2 < 2)
    (tableMeaning : TableMeaning (MontgomeryMeaning values) base 8 table) :
    BuildSpec (Execution.StepsAdmitted values)
      ((compilerWindows resolver commitment).choose b0 b1 b2 table)
      (fun result => MontgomeryMeaning values result ((PedersenWindows.selectorIndex s0 s1 s2+1) • base)) := by
  let ids := muxIDs b0 b1 b2 table
  let i := ids.map (values[·]!)
  have heads := muxInputs_bits values b0 b1 b2 table
  have firstValue : i[0]! = s0 := heads.1.trans first
  have secondValue : i[1]! = s1 := heads.2.1.trans second
  have thirdValue : i[2]! = s2 := heads.2.2.trans third
  have admitted : Primitive.Kind.multiMux3.Admitted i := ⟨by rw [firstValue]; exact bit0,
    by rw [secondValue]; exact bit1,by rw [thirdValue]; exact bit2⟩
  have size : ids.size=Primitive.Kind.multiMux3.inputCount := by
    simp only [ids,muxIDs,Array.size_append,Array.size_map,tableMeaning.1]
    rfl
  change BuildSpec _ (do
    let outputs ← operation resolver Primitive.Kind.multiMux3.tag ids
    return (outputs[17]!,outputs[18]!)) _
  apply buildSpec_bind _ _ _ _ _ (operation_spec resolver inputs values denotes .multiMux3 ids size admitted)
  intro outputs mapped
  apply buildSpec_pure
  have bound : PedersenWindows.selectorIndex s0 s1 s2<8 := by unfold PedersenWindows.selectorIndex; omega
  have tableCoordinates := muxInputs_coordinates values b0 b1 b2 table tableMeaning.1
    (PedersenWindows.selectorIndex s0 s1 s2) bound
  have selected := PedersenWindows.multiMux3_selects_models i (by rw [firstValue]; exact bit0)
    (by rw [secondValue]; exact bit1) (by rw [thirdValue]; exact bit2)
  rw [firstValue,secondValue,thirdValue] at selected
  have x := mapped_index values outputs (Primitive.multiMux3 i)
    (by simpa only [Primitive.Kind.values] using mapped) 17 (by change 17<19; omega)
  have y := mapped_index values outputs (Primitive.multiMux3 i)
    (by simpa only [Primitive.Kind.values] using mapped) 18 (by change 18<19; omega)
  have xModel : model values[outputs[17]!]! = model values[table[PedersenWindows.selectorIndex s0 s1 s2]!.1]! := by
    calc
      _=model (Primitive.multiMux3 i)[17]! := congrArg model x
      _=model i[3+PedersenWindows.selectorIndex s0 s1 s2]! := selected.1
      _=_ := congrArg model tableCoordinates.1
  have yModel : model values[outputs[18]!]! = model values[table[PedersenWindows.selectorIndex s0 s1 s2]!.2]! := by
    calc
      _=model (Primitive.multiMux3 i)[18]! := congrArg model y
      _=model i[11+PedersenWindows.selectorIndex s0 s1 s2]! := selected.2
      _=_ := congrArg model tableCoordinates.2
  obtain ⟨curve,group⟩ := tableMeaning.2 _ bound
  refine ⟨by rw [xModel,yModel]; exact curve,?_⟩
  simpa only [xModel,yModel] using group

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.choose_spec
