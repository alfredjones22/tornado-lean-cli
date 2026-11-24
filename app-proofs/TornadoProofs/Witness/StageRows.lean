import TornadoProofs.Witness.PrimitiveRows
import TornadoProofs.Witness.Num2BitsRows
import TornadoProofs.Witness.MerkleRows
import TornadoProofs.Witness.Num2BitsPhases
import TornadoProofs.Witness.BasePhases
import TornadoProofs.Witness.MerkleMetadata

set_option autoImplicit false
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open Execution

theorem interpreted_of_fit (compiled : CompiledGraph) (state : SignalState)
    (assignment : Nat → Fr) (values : Array Nat)
    (roots : RootInterpretation compiled assignment values) (fit : NodeFits compiled state) :
    SignalInterpretation state assignment values := by
  intro index node assigned
  rw [roots index,fit index node assigned]

theorem base_stage_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (assignment : Nat → Fr) (constant : assignment 0=1)
    (roots : RootInterpretation compiledGraph assignment values)
    (state after : SignalState) (base : BaseSeed)
    (compiled : basePublicAction resolver base state=.ok after)
    (terminal : SourceState compiledGraph values after) (seed : LocalSystem)
    (valid : SystemSatisfied assignment seed) :
    SystemSatisfied assignment (seed.equality base.index (constantLinear base.value)) := by
  obtain ⟨node,resolved,written⟩ := bind_success (resolver.resolve (.constant base.value)) _ after compiled
  have value : values[node]! = base.value := Symbolic.resolve_sound resolver inputs values denotes _ _ resolved
  have meaning := interpreted_write state after assignment values canonical base.index node written
    terminal.1 (interpreted_of_fit compiledGraph after assignment values roots terminal.2)
  apply equality_emit assignment seed base.index _ valid
  rw [meaning,value,constantLinear_value assignment constant]

theorem primitive_stage_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (assignment : Nat → Fr) (constant : assignment 0=1)
    (roots : RootInterpretation compiledGraph assignment values)
    (rowValue : ∀ index,linearValue assignment (signalLinear resolver.nodes compiledGraph index)=assignment index)
    (state after : SignalState) (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (admitted : PrimitiveSourceAdmitted compiledGraph values primitive)
    (compiled : compilePrimitiveStage resolver state primitive=.ok after)
    (terminal : SourceState compiledGraph values after) (seed result : LocalSystem)
    (valid : SystemSatisfied assignment seed)
    (generated : primitiveLocalSystem resolver.nodes compiledGraph seed primitive=.ok result) :
    SystemSatisfied assignment result := by
  have fit := nodeFits_backwards compiledGraph state after
    (compilePrimitiveStage_extends resolver state after primitive compiled) terminal.2
  obtain ⟨kind,tag⟩ := primitive_stage_kind resolver state after primitive compiled
  have arithmetic : ∀ inputs,primitive.inputs.mapM state.read=.ok inputs →
      kind.Admitted (inputs.map (values[·]!)) := by
    intro inputs read
    rw [nodeFits_inputs compiledGraph state fit primitive.inputs inputs read]
    simpa only [Array.map_map,Function.comp_def] using admitted kind tag
  exact compilePrimitiveStage_localRows resolver inputs values denotes (canonical_lookup values canonical)
    state after primitive kind tag arithmetic compiled terminal.1 compiledGraph assignment constant
    (interpreted_of_fit compiledGraph after assignment values roots terminal.2) rowValue seed result valid generated

theorem bits_stage_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (assignment : Nat → Fr) (constant : assignment 0=1)
    (roots : RootInterpretation compiledGraph assignment values)
    (rowValue : ∀ index,linearValue assignment (signalLinear resolver.nodes compiledGraph index)=assignment index)
    (state after : SignalState) (component : Num2BitsComponent)
    (admitted : BitSourceAdmitted compiledGraph values component)
    (compiled : compileNum2Bits resolver state component=.ok after)
    (terminal : SourceState compiledGraph values after) (seed result : LocalSystem)
    (valid : SystemSatisfied assignment seed)
    (generated : num2BitsLocalSystem resolver.nodes compiledGraph seed component=.ok result) :
    SystemSatisfied assignment result := by
  have fit := nodeFits_backwards compiledGraph state after
    (compileNum2Bits_extends resolver state after component compiled) terminal.2
  have bounded : ∀ input,state.read component.input=.ok input → values[input]! < 2^248 := by
    intro input read
    have same := fit component.input input (signalRead_slot state component.input input read)
    simpa only [BitSourceAdmitted,same] using admitted
  exact compileNum2Bits_localRows resolver inputs values denotes (canonical_lookup values canonical)
    state after component bounded compiled terminal.1 compiledGraph assignment constant
    (interpreted_of_fit compiledGraph after assignment values roots terminal.2) rowValue seed result valid generated

theorem merkle_stage_localRows (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (compiledGraph : CompiledGraph) (assignment : Nat → Fr) (constant : assignment 0=1)
    (roots : RootInterpretation compiledGraph assignment values)
    (rowValue : ∀ index,linearValue assignment (signalLinear resolver.nodes compiledGraph index)=assignment index)
    (constants : Array Nat) (state after : SignalState) (level : MerkleLevel) (sponge : SpongeLevel)
    (admitted : MerkleSourceAdmitted compiledGraph values level)
    (compiled : compileMerkleLevel resolver constants state level sponge=.ok after)
    (terminal : SourceState compiledGraph values after) (seed : LocalSystem)
    (valid : SystemSatisfied assignment seed) :
    SystemSatisfied assignment (merkleLocalSystem resolver.nodes compiledGraph constants seed level sponge) := by
  have fit := nodeFits_backwards compiledGraph state after
    (compileMerkleLevel_signalExtends resolver constants state after level sponge compiled) terminal.2
  have selector : SelectorBit state level values := by
    intro node read
    have same := fit level.selector node (signalRead_slot state level.selector node read)
    simpa only [MerkleSourceAdmitted,same] using admitted
  exact merkleLocalSystem_sound resolver inputs values denotes canonical compiledGraph constants state after
    level sponge assignment constant rowValue compiled selector terminal.1
    (interpreted_of_fit compiledGraph after assignment values roots terminal.2) seed valid

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.interpreted_of_fit
#print axioms TornadoProofs.Witness.Local.base_stage_localRows
#print axioms TornadoProofs.Witness.Local.primitive_stage_localRows
#print axioms TornadoProofs.Witness.Local.bits_stage_localRows
#print axioms TornadoProofs.Witness.Local.merkle_stage_localRows
