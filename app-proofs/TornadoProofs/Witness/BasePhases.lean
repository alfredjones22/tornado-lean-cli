import TornadoProofs.Witness.PrimitivePhases
import TornadoProofs.Witness.ActionPhases

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic
open Symbolic

def basePublicAction (resolver : Resolver) (base : BaseSeed) (state : SignalState) :
    Except String SignalState := do
  let node ← resolver.resolve (.constant base.value)
  state.write base.index node

theorem base_stage_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (finalRoots : CompiledGraph) (base : BaseSeed) (state after : SignalState)
    (compiled : basePublicAction resolver base state=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      (realize state values).write base.index base.value=.ok (realize after values) := by
  obtain ⟨node,resolved,written⟩ := bind_success (resolver.resolve (.constant base.value)) _ after compiled
  have value : values[node]! = base.value :=
    resolve_sound resolver inputs values denotes (.constant base.value) node resolved
  have actual := signalWrite_realize state after values base.index node written (canonical _) terminal.1
  have previous : SourceState finalRoots values state :=
    ⟨signalWrite_aliases_backwards state after values _ _ written terminal.1,
      nodeFits_backwards finalRoots state after (signalWrite_extends state after _ _ written) terminal.2⟩
  exact ⟨previous,by simpa only [value] using actual⟩

theorem base_phase_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (finalRoots : CompiledGraph) (bases : Array BaseSeed) (state after : SignalState)
    (compiled : forIn bases state (fun base current => do
      let next ← basePublicAction resolver base current
      pure (ForInStep.yield next))=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      forIn bases (realize state values) (fun (base : BaseSeed) (current : Assignment) => do
        let next ← current.write base.index base.value
        pure (ForInStep.yield next))=.ok (realize after values) := by
  apply action_phase_construct bases (basePublicAction resolver)
    (fun (base : BaseSeed) (state : Assignment) => state.write base.index base.value) values
    (SourceState finalRoots values) _ state after compiled terminal
  intro base member before after returned terminal
  exact base_stage_construct resolver inputs values denotes canonical finalRoots base before after returned terminal

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.base_stage_construct
#print axioms TornadoProofs.Witness.Execution.base_phase_construct
