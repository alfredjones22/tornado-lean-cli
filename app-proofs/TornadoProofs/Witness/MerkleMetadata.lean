import TornadoProofs.Witness.FeistelSignalExtends
import TornadoProofs.Witness.PrimitivePhases
import TornadoProofs.Witness.ActionPhases
import TornadoProofs.Witness.SpongeSimulation

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

theorem compileDualMux_signalExtends (resolver : Resolver) (state : SignalState)
    (level : MerkleLevel) (output : SignalState × Nat × Nat)
    (compiled : compileDualMux resolver state level=.ok output) : SignalExtends state output.1 := by
  unfold compileDualMux at compiled
  obtain ⟨leftInput,_,compiled⟩ := bind_success _ _ output compiled
  obtain ⟨rightInput,_,compiled⟩ := bind_success _ _ output compiled
  obtain ⟨selector,_,compiled⟩ := bind_success _ _ output compiled
  obtain ⟨left,_,compiled⟩ := bind_success _ _ output compiled
  obtain ⟨right,_,compiled⟩ := bind_success _ _ output compiled
  obtain ⟨first,firstBuilt,compiled⟩ := bind_success _ _ output compiled
  obtain ⟨second,secondBuilt,compiled⟩ := bind_success _ _ output compiled
  have equal : (second,left,right)=output := Except.ok.inj compiled
  rw [← equal]
  exact signalExtends_trans (signalWrite_extends _ _ _ _ firstBuilt)
    (signalWrite_extends _ _ _ _ secondBuilt)

theorem compileMerkleLevel_signalExtends (resolver : Resolver) (constants : Array Nat)
    (state after : SignalState) (level : MerkleLevel) (sponge : SpongeLevel)
    (compiled : compileMerkleLevel resolver constants state level sponge=.ok after) :
    SignalExtends state after := by
  unfold compileMerkleLevel at compiled
  obtain ⟨dual,dualBuilt,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨zeroNode,_,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨firstKey,firstKeyBuilt,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨firstLeft,firstLeftBuilt,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨firstInputs,firstInputsBuilt,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨first,firstBuilt,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨intermediateLeft,_,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨intermediateRight,_,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨secondKey,secondKeyBuilt,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨absorbed,_,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨secondLeft,secondLeftBuilt,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨secondInputs,secondInputsBuilt,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨second,secondBuilt,compiled⟩ := bind_success _ _ after compiled
  obtain ⟨hash,_,compiled⟩ := bind_success _ _ after compiled
  have result := compileDualMux_signalExtends resolver state level dual dualBuilt
  have result := signalExtends_trans result (signalWrite_extends _ _ _ _ firstKeyBuilt)
  have result := signalExtends_trans result (signalWrite_extends _ _ _ _ firstLeftBuilt)
  have result := signalExtends_trans result (signalWrite_extends _ _ _ _ firstInputsBuilt)
  have result := signalExtends_trans result (Local.compileFeistel_signalExtends resolver constants _ _ _ firstBuilt)
  have result := signalExtends_trans result (signalWrite_extends _ _ _ _ secondKeyBuilt)
  have result := signalExtends_trans result (signalWrite_extends _ _ _ _ secondLeftBuilt)
  have result := signalExtends_trans result (signalWrite_extends _ _ _ _ secondInputsBuilt)
  have result := signalExtends_trans result (Local.compileFeistel_signalExtends resolver constants _ _ _ secondBuilt)
  exact signalExtends_trans result (signalWrite_extends _ _ _ _ compiled)

def MerkleSourceAdmitted (compiled : CompiledGraph) (values : Array Nat)
    (level : MerkleLevel) : Prop := values[compiled.signalRoots[level.selector]!]! ≤ 1

theorem merkle_stage_source_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (constants : Array Nat) (finalRoots : CompiledGraph) (state after : SignalState)
    (level : MerkleLevel) (sponge : SpongeLevel)
    (admitted : MerkleSourceAdmitted finalRoots values level)
    (compiled : compileMerkleLevel resolver constants state level sponge=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      executeMerkleLevel constants (realize state values) level sponge=.ok (realize after values) := by
  have fit := nodeFits_backwards finalRoots state after
    (compileMerkleLevel_signalExtends resolver constants state after level sponge compiled) terminal.2
  have selector : SelectorBit state level values := by
    intro node read
    have same := fit level.selector node (signalRead_slot state level.selector node read)
    simpa only [MerkleSourceAdmitted,same] using admitted
  have result := compileMerkleLevel_construct resolver inputs values denotes canonical constants
    state after level sponge compiled selector terminal.1
  exact ⟨⟨result.1,fit⟩,result.2⟩

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.compileDualMux_signalExtends
#print axioms TornadoProofs.Witness.Execution.compileMerkleLevel_signalExtends
#print axioms TornadoProofs.Witness.Execution.merkle_stage_source_construct
