import TornadoProofs.Witness.StageRows
import TornadoProofs.Witness.RowPhases

set_option autoImplicit false
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open Execution

theorem bits_phase_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (assignment : Nat → Fr) (constant : assignment 0=1)
    (roots : RootInterpretation compiledGraph assignment values)
    (rowValue : ∀ index,linearValue assignment (signalLinear resolver.nodes compiledGraph index)=assignment index)
    (components : Array Num2BitsComponent)
    (admitted : ∀ component∈components,BitSourceAdmitted compiledGraph values component)
    (state after : SignalState) (seed result : LocalSystem)
    (compiled : forIn components state (fun component current => do
      let next ← compileNum2Bits resolver current component
      pure (ForInStep.yield next))=.ok after)
    (generated : forIn components seed (fun component current => do
      let next ← num2BitsLocalSystem resolver.nodes compiledGraph current component
      pure (ForInStep.yield next))=.ok result)
    (terminal : SourceState compiledGraph values after) (valid : SystemSatisfied assignment seed) :
    SystemSatisfied assignment result := by
  rw [←Array.forIn_toList] at compiled generated
  apply row_phase_sound components.toList (fun item before => compileNum2Bits resolver before item)
    (fun item before => num2BitsLocalSystem resolver.nodes compiledGraph before item)
    (SourceState compiledGraph values) (SystemSatisfied assignment) _ _ state after seed result
    compiled generated terminal valid
  · intro component member before after returned terminal
    exact (num2Bits_stage_source_construct resolver inputs values denotes (canonical_lookup values canonical)
      compiledGraph before after component (admitted component (by simpa using member)) returned terminal).1
  · intro component member before after returned terminal seed result generated valid
    exact bits_stage_localRows resolver inputs values denotes canonical compiledGraph assignment constant roots
      rowValue before after component (admitted component (by simpa using member)) returned terminal seed result valid generated

theorem primitive_phase_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (assignment : Nat → Fr) (constant : assignment 0=1)
    (roots : RootInterpretation compiledGraph assignment values)
    (rowValue : ∀ index,linearValue assignment (signalLinear resolver.nodes compiledGraph index)=assignment index)
    (primitives : Array Tornado.Protocol.WitnessVM.Primitive)
    (admitted : ∀ primitive∈primitives,PrimitiveSourceAdmitted compiledGraph values primitive)
    (state after : SignalState) (seed result : LocalSystem)
    (compiled : forIn primitives state (fun primitive current => do
      let next ← compilePrimitiveStage resolver current primitive
      pure (ForInStep.yield next))=.ok after)
    (generated : forIn primitives seed (fun primitive current => do
      let next ← primitiveLocalSystem resolver.nodes compiledGraph current primitive
      pure (ForInStep.yield next))=.ok result)
    (terminal : SourceState compiledGraph values after) (valid : SystemSatisfied assignment seed) :
    SystemSatisfied assignment result := by
  rw [←Array.forIn_toList] at compiled generated
  apply row_phase_sound primitives.toList (fun item before => compilePrimitiveStage resolver before item)
    (fun item before => primitiveLocalSystem resolver.nodes compiledGraph before item)
    (SourceState compiledGraph values) (SystemSatisfied assignment) _ _ state after seed result
    compiled generated terminal valid
  · intro primitive member before after returned terminal
    exact (primitive_stage_source_construct resolver inputs values denotes (canonical_lookup values canonical)
      compiledGraph before after primitive (admitted primitive (by simpa using member)) returned terminal).1
  · intro primitive member before after returned terminal seed result generated valid
    exact primitive_stage_localRows resolver inputs values denotes canonical compiledGraph assignment constant roots
      rowValue before after primitive (admitted primitive (by simpa using member)) returned terminal seed result valid generated

def baseRowAction (base : BaseSeed) (seed : LocalSystem) : Except String LocalSystem :=
  .ok (seed.equality base.index (constantLinear base.value))

theorem base_phase_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (assignment : Nat → Fr) (constant : assignment 0=1)
    (roots : RootInterpretation compiledGraph assignment values)
    (bases : Array BaseSeed) (state after : SignalState) (seed result : LocalSystem)
    (compiled : forIn bases state (fun base current => do
      let next ← basePublicAction resolver base current
      pure (ForInStep.yield next))=.ok after)
    (generated : forIn bases seed (fun base current => do
      let next ← baseRowAction base current
      pure (ForInStep.yield next))=.ok result)
    (terminal : SourceState compiledGraph values after) (valid : SystemSatisfied assignment seed) :
    SystemSatisfied assignment result := by
  rw [←Array.forIn_toList] at compiled generated
  apply row_phase_sound bases.toList (basePublicAction resolver) baseRowAction
    (SourceState compiledGraph values) (SystemSatisfied assignment) _ _ state after seed result
    compiled generated terminal valid
  · intro base member before after returned terminal
    exact (base_stage_construct resolver inputs values denotes (canonical_lookup values canonical)
      compiledGraph base before after returned terminal).1
  · intro base member before after returned terminal seed result generated valid
    have equal : seed.equality base.index (constantLinear base.value)=result := Except.ok.inj generated
    rw [←equal]
    exact base_stage_localRows resolver inputs values denotes canonical compiledGraph assignment constant roots
      before after base returned terminal seed valid

def merkleRowAction (nodes : Array Node) (compiled : CompiledGraph) (constants : Array Nat)
    (levels : Array MerkleLevel) (sponges : Array SpongeLevel) (index : Nat)
    (seed : LocalSystem) : Except String LocalSystem :=
  .ok (merkleLocalSystem nodes compiled constants seed levels[index]! sponges[index]!)

theorem merkle_phase_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (assignment : Nat → Fr) (constant : assignment 0=1)
    (roots : RootInterpretation compiledGraph assignment values)
    (rowValue : ∀ index,linearValue assignment (signalLinear resolver.nodes compiledGraph index)=assignment index)
    (constants : Array Nat) (levels : Array MerkleLevel) (sponges : Array SpongeLevel)
    (admitted : ∀ index<20,MerkleSourceAdmitted compiledGraph values levels[index]!)
    (state after : SignalState) (seed result : LocalSystem)
    (compiled : forIn (List.range 20) state (fun index current => do
      let next ← compileMerkleLevel resolver constants current levels[index]! sponges[index]!
      pure (ForInStep.yield next))=.ok after)
    (generated : forIn (List.range 20) seed (fun index current => do
      let next ← merkleRowAction resolver.nodes compiledGraph constants levels sponges index current
      pure (ForInStep.yield next))=.ok result)
    (terminal : SourceState compiledGraph values after) (valid : SystemSatisfied assignment seed) :
    SystemSatisfied assignment result := by
  apply row_phase_sound (List.range 20)
    (fun index before => compileMerkleLevel resolver constants before levels[index]! sponges[index]!)
    (merkleRowAction resolver.nodes compiledGraph constants levels sponges)
    (SourceState compiledGraph values) (SystemSatisfied assignment) _ _ state after seed result
    compiled generated terminal valid
  · intro index member before after returned terminal
    exact (merkle_stage_source_construct resolver inputs values denotes canonical constants
      compiledGraph before after levels[index]! sponges[index]! (admitted index (List.mem_range.mp member)) returned terminal).1
  · intro index member before after returned terminal seed result generated valid
    have equal : merkleLocalSystem resolver.nodes compiledGraph constants seed levels[index]! sponges[index]! = result :=
      Except.ok.inj generated
    rw [←equal]
    exact merkle_stage_localRows resolver inputs values denotes canonical compiledGraph assignment constant roots
      rowValue constants before after levels[index]! sponges[index]! (admitted index (List.mem_range.mp member)) returned terminal seed valid

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.bits_phase_localRows
#print axioms TornadoProofs.Witness.Local.primitive_phase_localRows
#print axioms TornadoProofs.Witness.Local.base_phase_localRows
#print axioms TornadoProofs.Witness.Local.merkle_phase_localRows
