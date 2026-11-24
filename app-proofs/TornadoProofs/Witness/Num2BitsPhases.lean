import TornadoProofs.Witness.Num2BitsSimulation
import TornadoProofs.Witness.PrimitivePhases
import TornadoProofs.Witness.ActionPhases

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic
open Symbolic

def BitSourceAdmitted (compiled : CompiledGraph) (values : Array Nat)
    (component : Num2BitsComponent) : Prop :=
  values[compiled.signalRoots[component.input]!]! < 2^248

theorem num2Bits_stage_source_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (finalRoots : CompiledGraph) (state after : SignalState) (component : Num2BitsComponent)
    (admitted : BitSourceAdmitted finalRoots values component)
    (compiled : compileNum2Bits resolver state component=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      executeNum2Bits (realize state values) component=.ok (realize after values) := by
  have fit := nodeFits_backwards finalRoots state after
    (compileNum2Bits_extends resolver state after component compiled) terminal.2
  have sourceBound : ∀ input, state.read component.input=.ok input → values[input]! < 2^248 := by
    intro input read
    have same := fit component.input input (signalRead_slot state component.input input read)
    simpa only [BitSourceAdmitted,same] using admitted
  have made := compileNum2Bits_construct resolver inputs values denotes canonical
    state after component sourceBound compiled terminal.1
  exact ⟨⟨made.1,fit⟩,made.2⟩

theorem num2Bits_phase_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (finalRoots : CompiledGraph) (components : Array Num2BitsComponent)
    (admitted : ∀ component ∈ components, BitSourceAdmitted finalRoots values component)
    (state after : SignalState)
    (compiled : forIn components state (fun component current => do
      let next ← compileNum2Bits resolver current component
      pure (ForInStep.yield next))=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      forIn components (realize state values) (fun component current => do
        let next ← executeNum2Bits current component
        pure (ForInStep.yield next))=.ok (realize after values) := by
  apply action_phase_construct components (fun component state => compileNum2Bits resolver state component)
    (fun component state => executeNum2Bits state component) values
    (SourceState finalRoots values) _ state after compiled terminal
  intro component member before after returned terminal
  exact num2Bits_stage_source_construct resolver inputs values denotes canonical finalRoots
    before after component (admitted component member) returned terminal

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.num2Bits_stage_source_construct
#print axioms TornadoProofs.Witness.Execution.num2Bits_phase_construct
