import TornadoProofs.Witness.MetadataState
import TornadoProofs.Witness.PrimitiveMetadata

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic
open Primitive Symbolic

def PrimitiveSourceAdmitted (compiled : CompiledGraph) (values : Array Nat)
    (primitive : Tornado.Protocol.WitnessVM.Primitive) : Prop :=
  ∀ kind : Kind, primitive.kind=kind.tag →
    kind.Admitted (primitive.inputs.map fun index => values[compiled.signalRoots[index]!]!)

def SourceState (compiled : CompiledGraph) (values : Array Nat) (state : SignalState) : Prop :=
  AliasesValid state values ∧ NodeFits compiled state

theorem primitive_stage_kind (resolver : Resolver) (state after : SignalState)
    (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (compiled : compilePrimitiveStage resolver state primitive=.ok after) :
    ∃ kind : Kind, primitive.kind=kind.tag := by
  by_cases shape : primitive.shapeValid state.slots.size=true
  · obtain ⟨kind,tag,_⟩ := primitive_shape_kind primitive state.slots.size shape
    exact ⟨kind,tag⟩
  · have invalid := Bool.eq_false_of_not_eq_true shape
    simp [compilePrimitiveStage,invalid,bind,Except.bind] at compiled

theorem primitive_stage_source_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (finalRoots : CompiledGraph) (state after : SignalState)
    (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (admitted : PrimitiveSourceAdmitted finalRoots values primitive)
    (compiled : compilePrimitiveStage resolver state primitive=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      evaluatePrimitive (realize state values) primitive=.ok (realize after values) := by
  have fit := nodeFits_backwards finalRoots state after
    (compilePrimitiveStage_extends resolver state after primitive compiled) terminal.2
  obtain ⟨kind,tag⟩ := primitive_stage_kind resolver state after primitive compiled
  have arithmetic : ∀ roots, primitive.inputs.mapM state.read=.ok roots →
      kind.Admitted (roots.map (values[·]!)) := by
    intro roots read
    rw [nodeFits_inputs finalRoots state fit primitive.inputs roots read]
    simpa only [Array.map_map,Function.comp_def] using admitted kind tag
  have made := compilePrimitiveStage_construct resolver inputs values denotes canonical
    state after primitive kind tag arithmetic compiled terminal.1
  exact ⟨⟨made.1,fit⟩,made.2⟩

theorem primitive_phase_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (finalRoots : CompiledGraph) (primitives : Array Tornado.Protocol.WitnessVM.Primitive)
    (admitted : ∀ primitive ∈ primitives, PrimitiveSourceAdmitted finalRoots values primitive)
    (state after : SignalState)
    (compiled : forIn primitives state (fun primitive current => do
      let next ← compilePrimitiveStage resolver current primitive
      pure (ForInStep.yield next))=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      forIn primitives (realize state values) (fun primitive current => do
        let next ← evaluatePrimitive current primitive
        pure (ForInStep.yield next))=.ok (realize after values) := by
  rw [← Array.forIn_toList] at compiled ⊢
  apply forIn_construct_from_public_mem primitives.toList _ _ (fun state => realize state values)
    (SourceState finalRoots values) _ _ state after compiled terminal
  · intro primitive member before next returned terminal
    obtain ⟨middle,stage,after⟩ := bind_success
      (compilePrimitiveStage resolver before primitive)
      (fun next => pure (ForInStep.yield next)) next returned
    have same : ForInStep.yield middle=next := by
      simpa only [pure,Except.pure,Except.ok.injEq] using after
    subst next
    exact (primitive_stage_source_construct resolver inputs values denotes canonical finalRoots
      before middle primitive (admitted primitive (by simpa using member)) stage terminal).1
  · intro primitive member before next returned terminal
    obtain ⟨middle,stage,after⟩ := bind_success
      (compilePrimitiveStage resolver before primitive)
      (fun next => pure (ForInStep.yield next)) next returned
    have same : ForInStep.yield middle=next := by
      simpa only [pure,Except.pure,Except.ok.injEq] using after
    subst next
    have made := primitive_stage_source_construct resolver inputs values denotes canonical finalRoots
      before middle primitive (admitted primitive (by simpa using member)) stage terminal
    simp only [made.2,bind,Except.bind,pure,Except.pure,mapStep]

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.primitive_stage_kind
#print axioms TornadoProofs.Witness.Execution.primitive_stage_source_construct
#print axioms TornadoProofs.Witness.Execution.primitive_phase_construct
