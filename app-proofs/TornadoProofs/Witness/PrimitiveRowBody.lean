import TornadoProofs.Witness.PrimitiveRowEquations
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open TornadoProofs.Witness.Primitive

theorem input_row_value (nodes : Array Node) (compiled : CompiledGraph)
    (assignment : Nat → Fr)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiled index)=assignment index)
    (p : Tornado.Protocol.WitnessVM.Primitive) (i : Array Nat)
    (meaning : ∀ j, j<p.inputs.size → assignment p.inputs[j]! =model i[j]!)
    (j : Nat) (bound : j<p.inputs.size) :
    linearValue assignment ((p.inputs.map (signalLinear nodes compiled))[j]?.getD []) = model i[j]! := by
  rw [Array.getElem?_map,Array.getElem?_eq_getElem bound]
  simpa only [Option.map_some,Option.getD_some,getElem!_pos p.inputs j bound,rowValue] using meaning j bound

theorem primitiveSimpleBody_sound (nodes : Array Node) (compiledGraph : CompiledGraph)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiledGraph index)=assignment index)
    (p : Tornado.Protocol.WitnessVM.Primitive) (kind : Kind) (i o : Array Nat)
    (tag : p.kind=kind.tag) (simple : kind≠.multiMux3)
    (inputSize : p.inputs.size=kind.inputCount) (outputSize : p.outputs.size=kind.count)
    (inputMeaning : ∀ j, j<p.inputs.size → assignment p.inputs[j]! = model i[j]!)
    (outputMeaning : ∀ j, j<p.outputs.size → assignment p.outputs[j]! = model o[j]!)
    (equations : KindEquations kind i o)
    (seed after : LocalSystem) (valid : SystemSatisfied assignment seed)
    (returned : primitiveBody nodes compiledGraph seed p=.ok after) :
    SystemSatisfied assignment after := by
  cases kind with
  | montgomeryAdd =>
    have inSize : p.inputs.size=4 := inputSize
    have outSize : p.outputs.size=3 := outputSize
    have in0 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 0 (by omega)
    have in1 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 1 (by omega)
    have in2 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 2 (by omega)
    have in3 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 3 (by omega)
    have out0 := outputMeaning 0 (by omega)
    have out1 := outputMeaning 1 (by omega)
    have out2 := outputMeaning 2 (by omega)
    simp only [primitiveBody,tag,Kind.tag,pure,Except.pure,Except.ok.injEq] at returned
    rw [←returned]
    refine constraint_emit assignment constant _ _ _ _ (constraint_emit assignment constant _ _ _ _ (constraint_emit assignment constant _ _ _ _ (valid) ?_) ?_) ?_
    all_goals simp only [in0, in1, in2, in3, rowValue, out0, out1, out2, constantLinear_value assignment constant, sumLinear_value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, linear_add, linear_scale,negative_one]
    all_goals simp only [KindEquations,MontgomeryAddEquations] at equations
    all_goals rcases equations with ⟨e0,e1,e2⟩
    all_goals norm_num only [model, Nat.cast_ofNat] at *
    · linear_combination e0
    · linear_combination e1
    · linear_combination e2
  | montgomeryDouble =>
    have inSize : p.inputs.size=2 := inputSize
    have outSize : p.outputs.size=4 := outputSize
    have in0 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 0 (by omega)
    have in1 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 1 (by omega)
    have out0 := outputMeaning 0 (by omega)
    have out1 := outputMeaning 1 (by omega)
    have out2 := outputMeaning 2 (by omega)
    have out3 := outputMeaning 3 (by omega)
    simp only [primitiveBody,tag,Kind.tag,pure,Except.pure,Except.ok.injEq] at returned
    rw [←returned]
    refine constraint_emit assignment constant _ _ _ _ (constraint_emit assignment constant _ _ _ _ (constraint_emit assignment constant _ _ _ _ (product_emit assignment constant _ _ _ _ (valid) ?_) ?_) ?_) ?_
    all_goals simp only [in0, in1, rowValue, out0, out1, out2, out3, constantLinear_value assignment constant, sumLinear_value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, linear_add, linear_scale,negative_one]
    all_goals simp only [KindEquations,MontgomeryDoubleEquations] at equations
    all_goals rcases equations with ⟨e0,e1,e2,e3⟩
    all_goals norm_num only [model, Nat.cast_ofNat] at *
    · linear_combination -e0
    · linear_combination e1
    · linear_combination e2
    · linear_combination e3
  | edwards2Montgomery =>
    have inSize : p.inputs.size=2 := inputSize
    have outSize : p.outputs.size=2 := outputSize
    have in0 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 0 (by omega)
    have in1 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 1 (by omega)
    have out0 := outputMeaning 0 (by omega)
    have out1 := outputMeaning 1 (by omega)
    simp only [primitiveBody,tag,Kind.tag,pure,Except.pure,Except.ok.injEq] at returned
    rw [←returned]
    refine constraint_emit assignment constant _ _ _ _ (constraint_emit assignment constant _ _ _ _ (valid) ?_) ?_
    all_goals simp only [in0, in1, rowValue, out0, out1, constantLinear_value assignment constant, linear_add, linear_scale,negative_one]
    all_goals simp only [KindEquations,Edwards2MontgomeryEquations] at equations
    all_goals rcases equations with ⟨e0,e1⟩
    all_goals norm_num only [model, Nat.cast_ofNat] at *
    · linear_combination e0
    · linear_combination e1
  | montgomery2Edwards =>
    have inSize : p.inputs.size=2 := inputSize
    have outSize : p.outputs.size=2 := outputSize
    have in0 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 0 (by omega)
    have in1 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 1 (by omega)
    have out0 := outputMeaning 0 (by omega)
    have out1 := outputMeaning 1 (by omega)
    simp only [primitiveBody,tag,Kind.tag,pure,Except.pure,Except.ok.injEq] at returned
    rw [←returned]
    refine constraint_emit assignment constant _ _ _ _ (constraint_emit assignment constant _ _ _ _ (valid) ?_) ?_
    all_goals simp only [in0, in1, rowValue, out0, out1, constantLinear_value assignment constant, linear_add, linear_scale,negative_one]
    all_goals simp only [KindEquations,Montgomery2EdwardsEquations] at equations
    all_goals rcases equations with ⟨e0,e1⟩
    all_goals norm_num only [model, Nat.cast_ofNat] at *
    · linear_combination e0
    · linear_combination e1
  | babyAdd =>
    have inSize : p.inputs.size=4 := inputSize
    have outSize : p.outputs.size=6 := outputSize
    have in0 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 0 (by omega)
    have in1 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 1 (by omega)
    have in2 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 2 (by omega)
    have in3 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 3 (by omega)
    have out0 := outputMeaning 0 (by omega)
    have out1 := outputMeaning 1 (by omega)
    have out2 := outputMeaning 2 (by omega)
    have out3 := outputMeaning 3 (by omega)
    have out4 := outputMeaning 4 (by omega)
    have out5 := outputMeaning 5 (by omega)
    simp only [primitiveBody,tag,Kind.tag,pure,Except.pure,Except.ok.injEq] at returned
    rw [←returned]
    refine constraint_emit assignment constant _ _ _ _ (constraint_emit assignment constant _ _ _ _ (product_emit assignment constant _ _ _ _ (constraint_emit assignment constant _ _ _ _ (product_emit assignment constant _ _ _ _ (product_emit assignment constant _ _ _ _ (valid) ?_) ?_) ?_) ?_) ?_) ?_
    all_goals simp only [in0, in1, in2, in3, rowValue, out0, out1, out2, out3, out4, out5, constantLinear_value assignment constant, linear_add, linear_scale,negative_one]
    all_goals simp only [KindEquations,BabyAddEquations] at equations
    all_goals rcases equations with ⟨e0,e1,e2,e3,e4,e5⟩
    all_goals norm_num only [model, Nat.cast_ofNat] at *
    · linear_combination -e0
    · linear_combination -e1
    · linear_combination -e2
    · linear_combination -e3
    · linear_combination e4
    · linear_combination e5
  | window4 =>
    have inSize : p.inputs.size=2 := inputSize
    have outSize : p.outputs.size=1 := outputSize
    have in0 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 0 (by omega)
    have in1 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 1 (by omega)
    have out0 := outputMeaning 0 (by omega)
    simp only [primitiveBody,tag,Kind.tag,pure,Except.pure,Except.ok.injEq] at returned
    rw [←returned]
    refine constraint_emit assignment constant _ _ _ _ (valid) ?_
    all_goals simp only [in0, in1, rowValue, out0, linear_add, linear_scale,negative_one]
    all_goals simp only [KindEquations,Window4Equations] at equations
    all_goals norm_num only [model, Nat.cast_ofNat] at *
    · linear_combination equations
  | square =>
    have inSize : p.inputs.size=1 := inputSize
    have outSize : p.outputs.size=1 := outputSize
    have in0 := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 0 (by omega)
    have out0 := outputMeaning 0 (by omega)
    simp only [primitiveBody,tag,Kind.tag,pure,Except.pure,Except.ok.injEq] at returned
    rw [←returned]
    refine product_emit assignment constant _ _ _ _ (valid) ?_
    all_goals simp only [in0, out0]
    all_goals simp only [KindEquations,SquareEquations] at equations
    all_goals norm_num only [model, Nat.cast_ofNat] at *
    · linear_combination -equations
  | multiMux3 => exact False.elim (simple rfl)

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.input_row_value
#print axioms TornadoProofs.Witness.Local.primitiveSimpleBody_sound
