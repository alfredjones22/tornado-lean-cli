import TornadoProofs.Witness.PrimitiveRowBody
import TornadoProofs.Witness.SignalWriteMany

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open TornadoProofs.Witness.Primitive

def muxRows (nodes : Array Node) (compiled : CompiledGraph)
    (p : Tornado.Protocol.WitnessVM.Primitive) (coordinate : Nat) (result : LocalSystem) : LocalSystem :=
  let row := signalLinear nodes compiled
  let input := p.inputs.map row
  let output := fun i => row p.outputs[i]!
  let c := fun i => input[3+coordinate*8+i]!
  let index := fun i => p.outputs[1+i*2+coordinate]!
  let out := fun i => row (index i)
  let a210 := sumLinear [c 7,negLinear (c 6),negLinear (c 5),c 4,
    negLinear (c 3),c 2,c 1,negLinear (c 0)]
  let result := result.product (index 0) a210 (output 0)
  let result := result.product (index 1) (sumLinear [c 6,negLinear (c 4),negLinear (c 2),c 0]) input[1]!
  let result := result.product (index 2) (sumLinear [c 5,negLinear (c 4),negLinear (c 1),c 0]) input[0]!
  let result := result.equality (index 3) (minusLinear (c 4) (c 0))
  let result := result.product (index 4) (sumLinear [c 3,negLinear (c 2),negLinear (c 1),c 0]) (output 0)
  let result := result.product (index 5) (minusLinear (c 2) (c 0)) input[1]!
  let result := result.product (index 6) (minusLinear (c 1) (c 0)) input[0]!
  let result := result.equality (index 7) (c 0)
  let result := result.constraint (sumLinear [out 0,out 1,out 2,out 3]) input[2]!
    (minusLinear (out 8) (sumLinear [out 4,out 5,out 6,c 0]))
  result

theorem muxBody_source (nodes : Array Node) (compiled : CompiledGraph)
    (p : Tornado.Protocol.WitnessVM.Primitive) (tag : p.kind="MultiMux3") (seed : LocalSystem) :
    primitiveBody nodes compiled seed p =
      .ok (muxRows nodes compiled p 1 (muxRows nodes compiled p 0
        (seed.product p.outputs[0]! (p.inputs.map (signalLinear nodes compiled))[1]!
          (p.inputs.map (signalLinear nodes compiled))[0]!))) := by
  simp only [primitiveBody,tag]
  rw [Execution.forIn_range_zero]
  simp only [show List.range 2=[0,1] from rfl,List.forIn_cons,List.forIn_nil,bind,Except.bind,pure,Except.pure]
  rfl

theorem muxRows_sound (nodes : Array Node) (compiledGraph : CompiledGraph)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiledGraph index)=assignment index)
    (p : Tornado.Protocol.WitnessVM.Primitive) (i o : Array Nat) (coordinate : Nat)
    (coordBound : coordinate<2) (inputSize : p.inputs.size=19) (outputSize : p.outputs.size=19)
    (inputMeaning : ∀ j, j<p.inputs.size → assignment p.inputs[j]! = model i[j]!)
    (outputMeaning : ∀ j, j<p.outputs.size → assignment p.outputs[j]! = model o[j]!)
    (selector : model o[0]! = model i[1]! * model i[0]!)
    (equations : CoordinateEquations i coordinate i[0]! i[1]! i[2]!
      (TornadoProofs.Witness.Field.mul i[1]! i[0]!) (coordinateAt o coordinate))
    (seed : LocalSystem) (valid : SystemSatisfied assignment seed) :
    SystemSatisfied assignment (muxRows nodes compiledGraph p coordinate seed) := by
  let row := signalLinear nodes compiledGraph
  let input := p.inputs.map row
  have inputV (j : Nat) (bound : j<19) : linearValue assignment input[j]! = model i[j]! := by
    have known := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning j (by omega)
    simpa only [input,getElem!_def] using known
  have cV (j : Nat) (bound : j<8) :
      linearValue assignment input[3+coordinate*8+j]! = model i[3+coordinate*8+j]! :=
    inputV _ (by omega)
  have outV (j : Nat) (bound : j<9) :
      assignment p.outputs[1+j*2+coordinate]! = model o[1+j*2+coordinate]! :=
    outputMeaning _ (by omega)
  have c0 := cV 0 (by omega)
  have c1 := cV 1 (by omega)
  have c2 := cV 2 (by omega)
  have c3 := cV 3 (by omega)
  have c4 := cV 4 (by omega)
  have c5 := cV 5 (by omega)
  have c6 := cV 6 (by omega)
  have c7 := cV 7 (by omega)
  have o0 := outV 0 (by omega)
  have o1 := outV 1 (by omega)
  have o2 := outV 2 (by omega)
  have o3 := outV 3 (by omega)
  have o4 := outV 4 (by omega)
  have o5 := outV 5 (by omega)
  have o6 := outV 6 (by omega)
  have o7 := outV 7 (by omega)
  have o8 := outV 8 (by omega)
  have s0 := inputV 0 (by omega)
  have s1 := inputV 1 (by omega)
  have s2 := inputV 2 (by omega)
  have prod := outputMeaning 0 (by omega)
  have at0 : (coordinateAt o coordinate)[0]! = o[1+coordinate]! := rfl
  have at1 : (coordinateAt o coordinate)[1]! = o[3+coordinate]! := rfl
  have at2 : (coordinateAt o coordinate)[2]! = o[5+coordinate]! := rfl
  have at3 : (coordinateAt o coordinate)[3]! = o[7+coordinate]! := rfl
  have at4 : (coordinateAt o coordinate)[4]! = o[9+coordinate]! := rfl
  have at5 : (coordinateAt o coordinate)[5]! = o[11+coordinate]! := rfl
  have at6 : (coordinateAt o coordinate)[6]! = o[13+coordinate]! := rfl
  have at7 : (coordinateAt o coordinate)[7]! = o[15+coordinate]! := rfl
  have at8 : (coordinateAt o coordinate)[8]! = o[17+coordinate]! := rfl
  simp only [CoordinateEquations,at0,at1,at2,at3,at4,at5,at6,at7,at8,TornadoProofs.Witness.Field.model_mul] at equations
  rw [←selector] at equations
  rcases equations with ⟨e0,e1,e2,e3,e4,e5,e6,e7,e8⟩
  dsimp only [input,row] at c0 c1 c2 c3 c4 c5 c6 c7 o0 o1 o2 o3 o4 o5 o6 o7 o8 s0 s1 s2
  simp only [Nat.reduceMul,Nat.reduceAdd,Nat.add_zero] at c0 o0 o1 o2 o3 o4 o5 o6 o7 o8 e0 e1 e2 e3 e4 e5 e6 e7 e8
  unfold muxRows
  refine constraint_emit assignment constant _ _ _ _ (equality_emit assignment _ _ _ (product_emit assignment constant _ _ _ _ (product_emit assignment constant _ _ _ _ (product_emit assignment constant _ _ _ _ (equality_emit assignment _ _ _ (product_emit assignment constant _ _ _ _ (product_emit assignment constant _ _ _ _ (product_emit assignment constant _ _ _ _ (valid) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
  all_goals simp only [Nat.reduceMul,Nat.reduceAdd,c0, c1, c2, c3, c4, c5, c6, c7, o0, o1, o2, o3, o4, o5, o6, o7, o8, s0, s1, s2, rowValue, prod, linear_add, linear_scale, negative_one, sumLinear_value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  · linear_combination -e0
  · linear_combination -e1
  · linear_combination -e2
  · linear_combination e3
  · linear_combination -e4
  · linear_combination -e5
  · linear_combination -e6
  · linear_combination e7
  · linear_combination e8

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.muxBody_source
#print axioms TornadoProofs.Witness.Local.muxRows_sound
