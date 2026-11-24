import TornadoProofs.Witness.MuxRows
import TornadoProofs.Witness.PrimitiveConstantRows
import TornadoProofs.Witness.FeistelSupport
import TornadoProofs.Witness.PrimitiveRowMeaning

set_option autoImplicit false
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open TornadoProofs.Witness.Primitive

/-- The real local generator's complete output, including its constant-fold
rows, is satisfied by the original ordered primitive input/output values. -/
theorem primitiveLocalSystem_sound (nodes : Array Node) (compiledGraph : CompiledGraph)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiledGraph index)=assignment index)
    (p : Tornado.Protocol.WitnessVM.Primitive) (kind : Kind) (i o : Array Nat)
    (tag : p.kind=kind.tag)
    (inputSize : p.inputs.size=kind.inputCount) (outputSize : p.outputs.size=kind.count)
    (inputMeaning : ∀ j, j<p.inputs.size → assignment p.inputs[j]! = model i[j]!)
    (outputMeaning : ∀ j, j<p.outputs.size → assignment p.outputs[j]! = model o[j]!)
    (equations : KindEquations kind i o)
    (seed after : LocalSystem) (valid : SystemSatisfied assignment seed)
    (returned : primitiveLocalSystem nodes compiledGraph seed p=.ok after) :
    SystemSatisfied assignment after := by
  rw [primitiveLocalSystem_source] at returned
  obtain ⟨accumulated,folded,body⟩ := Execution.bind_success
    (forIn p.outputs.toList seed (constantRowEffect nodes compiledGraph)) _ after returned
  have accumulatedValid := constantRows_sound nodes compiledGraph assignment rowValue
    p.outputs.toList seed accumulated valid folded
  by_cases multi : kind=.multiMux3
  · subst kind
    rw [muxBody_source nodes compiledGraph p tag] at body
    have equal : muxRows nodes compiledGraph p 1 (muxRows nodes compiledGraph p 0
        (accumulated.product p.outputs[0]! (p.inputs.map (signalLinear nodes compiledGraph))[1]!
          (p.inputs.map (signalLinear nodes compiledGraph))[0]!))=after := Except.ok.inj body
    rw [←equal]
    rcases equations with ⟨product,first,second⟩
    apply muxRows_sound nodes compiledGraph assignment constant rowValue p i o 1 (by decide)
      inputSize outputSize inputMeaning outputMeaning product second
    apply muxRows_sound nodes compiledGraph assignment constant rowValue p i o 0 (by decide)
      inputSize outputSize inputMeaning outputMeaning product first
    apply product_emit assignment constant _ _ _ _ accumulatedValid
    have left := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 1
      (by rw [inputSize]; decide)
    have right := input_row_value nodes compiledGraph assignment rowValue p i inputMeaning 0
      (by rw [inputSize]; decide)
    have leftValue : linearValue assignment (p.inputs.map (signalLinear nodes compiledGraph))[1]! = model i[1]! := by
      simpa only [getElem!_def] using left
    have rightValue : linearValue assignment (p.inputs.map (signalLinear nodes compiledGraph))[0]! = model i[0]! := by
      simpa only [getElem!_def] using right
    rw [leftValue,rightValue,outputMeaning 0 (by rw [outputSize]; decide)]
    exact product.symm
  · exact primitiveSimpleBody_sound nodes compiledGraph assignment constant rowValue p kind i o
      tag multi inputSize outputSize inputMeaning outputMeaning equations accumulated after
      accumulatedValid body

/-- Inverse/selector conditions independently construct the primitive's
mathematical outputs and hence every emitted circuit row. -/
theorem primitiveLocalSystem_construct (nodes : Array Node) (compiledGraph : CompiledGraph)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (rowValue : ∀ index, linearValue assignment (signalLinear nodes compiledGraph index)=assignment index)
    (p : Tornado.Protocol.WitnessVM.Primitive) (kind : Kind) (i : Array Nat)
    (tag : p.kind=kind.tag)
    (inputSize : p.inputs.size=kind.inputCount) (outputSize : p.outputs.size=kind.count)
    (admitted : kind.Admitted i)
    (inputMeaning : ∀ j, j<p.inputs.size → assignment p.inputs[j]! = model i[j]!)
    (outputMeaning : ∀ j, j<p.outputs.size → assignment p.outputs[j]! = model (kind.values i)[j]!)
    (seed after : LocalSystem) (valid : SystemSatisfied assignment seed)
    (returned : primitiveLocalSystem nodes compiledGraph seed p=.ok after) :
    SystemSatisfied assignment after :=
  primitiveLocalSystem_sound nodes compiledGraph assignment constant rowValue p kind i (kind.values i)
    tag inputSize outputSize inputMeaning outputMeaning (kindValues_equations kind i admitted)
    seed after valid returned

/-- Public metadata compilation and independent DAG/source admissibility
construct satisfaction of the actual emitted primitive equations. -/
theorem compilePrimitiveStage_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (state after : SignalState) (p : Tornado.Protocol.WitnessVM.Primitive) (kind : Kind)
    (tag : p.kind=kind.tag)
    (admitted : ∀ roots, p.inputs.mapM state.read=.ok roots → kind.Admitted (roots.map (values[·]!)))
    (compiled : compilePrimitiveStage resolver state p=.ok after)
    (aliases : Execution.AliasesValid after values) (compiledGraph : CompiledGraph)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (interpreted : SignalInterpretation after assignment values)
    (rowValue : ∀ index, linearValue assignment (signalLinear resolver.nodes compiledGraph index)=assignment index)
    (seed result : LocalSystem) (valid : SystemSatisfied assignment seed)
    (generated : primitiveLocalSystem resolver.nodes compiledGraph seed p=.ok result) :
    SystemSatisfied assignment result := by
  obtain ⟨i,admissible,inputSize,outputSize,inputMeaning,outputMeaning⟩ :=
    primitive_stage_meaning resolver inputs values denotes canonical state after p kind tag
      admitted compiled aliases assignment interpreted
  exact primitiveLocalSystem_construct resolver.nodes compiledGraph assignment constant rowValue p kind i
    tag inputSize outputSize admissible inputMeaning outputMeaning seed result valid generated

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.primitiveLocalSystem_sound
#print axioms TornadoProofs.Witness.Local.primitiveLocalSystem_construct
#print axioms TornadoProofs.Witness.Local.compilePrimitiveStage_localRows
