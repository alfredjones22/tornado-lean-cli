import TornadoProofs.Witness.PrimitiveCompiler
import TornadoProofs.Witness.ReadRealization
import TornadoProofs.Witness.SignalWriteMany

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic
open Primitive Symbolic

theorem primitive_shape_dimensions (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (kind : Kind) (size : Nat) (tag : primitive.kind=kind.tag)
    (shape : primitive.shapeValid size=true) :
    primitive.inputs.size=kind.inputCount ∧ primitive.outputs.size=kind.count := by
  cases kind <;>
    simp [Tornado.Protocol.WitnessVM.Primitive.shapeValid,tag,Kind.tag,
      Bool.and_eq_true,beq_iff_eq] at shape
  all_goals exact ⟨shape.1.1.1,shape.1.1.2⟩

theorem evaluatePrimitive_outputLoop (state : Assignment)
    (primitive : Tornado.Protocol.WitnessVM.Primitive) (inputs outputs : Array Nat)
    (shape : primitive.shapeValid state.values.size=true)
    (read : readInputsFrom state primitive.inputs.toList #[]= .ok inputs)
    (arithmetic : primitiveValues primitive.kind inputs=.ok outputs)
    (count : outputs.size=primitive.outputs.size) :
    evaluatePrimitive state primitive = (do
      let mut result := state
      for i in [0:outputs.size] do
        result ← result.write primitive.outputs[i]! outputs[i]!
      pure result) := by
  simp only [evaluatePrimitive,shape,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rw [← Array.forIn_toList]
  change (do
    let inputs ← readInputsFrom state primitive.inputs.toList #[]
    let outputs ← primitiveValues primitive.kind inputs
    if outputs.size != primitive.outputs.size then
      throw s!"Circuit primitive {primitive.name} output count differs from metadata."
    let mut result := state
    for i in [0:outputs.size] do result ← result.write primitive.outputs[i]! outputs[i]!
    pure result) = _
  rw [read]
  simp only [bind,Except.bind]
  rw [arithmetic]
  have guard : (outputs.size != primitive.outputs.size)=false := by simp only [count,bne_self_eq_false]
  simp only [guard,Bool.false_eq_true,↓reduceIte,pure,Except.pure]

/-- All premises beyond public compiler success are independent field-value
conditions: canonical values, mathematical inverse/bit admissibility, and
commitment-source alias equality. Native helper acceptance is constructed. -/
theorem compilePrimitiveStage_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (state after : SignalState) (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (kind : Kind) (tag : primitive.kind=kind.tag)
    (admitted : ∀ roots, primitive.inputs.mapM state.read=.ok roots →
      kind.Admitted (roots.map (values[·]!)))
    (compiled : compilePrimitiveStage resolver state primitive=.ok after)
    (aliases : AliasesValid after values) :
    AliasesValid state values ∧
      evaluatePrimitive (realize state values) primitive=.ok (realize after values) := by
  by_cases shape : primitive.shapeValid state.slots.size=true
  · cases read : primitive.inputs.mapM state.read with
    | error err => simp [compilePrimitiveStage,shape,read,bind,Except.bind,pure,Except.pure] at compiled
    | ok roots =>
      cases built : compilePrimitive resolver primitive.kind roots with
      | error err => simp [compilePrimitiveStage,shape,read,built,bind,Except.bind,pure,Except.pure] at compiled
      | ok outputs =>
        have written : state.writeMany primitive.outputs outputs=.ok after := by
          simpa [compilePrimitiveStage,shape,read,built,bind,Except.bind,pure,Except.pure] using compiled
        have rootCount : roots.size=kind.inputCount :=
          (arrayMapM_size state.read primitive.inputs roots read).trans
            (primitive_shape_dimensions primitive kind state.slots.size tag shape).1
        have outputsValue := compilePrimitive_values resolver inputs values denotes kind roots outputs
          rootCount (admitted roots read) (by simpa only [tag] using built)
        have arithmetic := kind.construct (roots.map (values[·]!)) (admitted roots read)
        have nativeArithmetic : primitiveValues primitive.kind (roots.map (values[·]!))=
            .ok (outputs.map (values[·]!)) := by
          rw [tag,arithmetic,outputsValue]
        have nativeRead := readInputs_realize state values primitive.inputs roots read
        have count : primitive.outputs.size=outputs.size := by
          by_contra different
          simp [SignalState.writeMany,different,bind,Except.bind] at written
        have simulation := signalWriteMany_construct state after values primitive.outputs outputs
          written canonical aliases
        refine ⟨simulation.1,?_⟩
        rw [evaluatePrimitive_outputLoop _ _ _ _ (by simpa only [realize_size] using shape)
          nativeRead nativeArithmetic (by simpa only [Array.size_map] using count.symm)]
        simpa only [Array.size_map] using simulation.2
  · have invalid : primitive.shapeValid state.slots.size=false := Bool.eq_false_of_not_eq_true shape
    simp [compilePrimitiveStage,invalid,bind,Except.bind] at compiled

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.primitive_shape_dimensions
#print axioms TornadoProofs.Witness.Execution.evaluatePrimitive_outputLoop
#print axioms TornadoProofs.Witness.Execution.compilePrimitiveStage_construct
