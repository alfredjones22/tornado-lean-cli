import TornadoProofs.Witness.FootprintMeaning
import TornadoProofs.Witness.LayoutSlots

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.PedersenSchedule

theorem complete_read_root (state : SignalState) (compiled : CompiledGraph)
    (complete : state.slots=compiled.signalRoots.map some) (index node : Nat)
    (read : state.read index=.ok node) : node=compiled.signalRoots[index]! :=
  (complete_nodeFits state compiled complete index node (signalRead_slot state index node read)).symm

/-- Independent signed-window group semantics supply these three claims;
public structural admission transports them to the original graph. -/
structure PedersenSourceParts (graph : SelectedGraph) (compiled : CompiledGraph) (values : Array Nat) : Prop where
  aliases : ∀ pair∈compiled.commitmentAliases.toList,values[pair.1]! = values[pair.2]!
  primitives : ∀ primitive∈graph.primitives,PrimitiveSourceAdmitted compiled values primitive
  nullifier : values[compiled.publicNullifier.1]! = values[compiled.publicNullifier.2]!

theorem schedule_source_parts (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (certificate : CertifiedSchedule resolver graph compiled)
    (inputs : Array Nat) (commitment : Nat) (size : inputs.size=49) (constant : inputs[0]! = 1)
    (reference : Reference) (referenceBuilt : referenceSchedule resolver graph=.ok reference)
    (admitted : StepsAdmitted (sourceValues resolver inputs commitment) reference.steps)
    (nativeCommitment : (sourceValues resolver inputs commitment)[reference.commitment.1]! = commitment)
    (nativeNullifier : (sourceValues resolver inputs commitment)[reference.nullifier.1]! = inputs[2]!) :
    PedersenSourceParts graph compiled (sourceValues resolver inputs commitment) := by
  obtain ⟨other,actual,otherBuilt,observed,_,intended,count,newSource,nullifierSource⟩ :=
    certifiedSchedule_intended resolver graph compiled certificate
  have equal : other=reference := Except.ok.inj (otherBuilt.symm.trans referenceBuilt)
  subst other
  constructor
  · intro pair member
    have member' : pair∈compiled.commitmentAliases := Array.mem_toList_iff.mp member
    obtain ⟨index,bound,equal⟩ := Array.mem_iff_getElem.mp member'
    have zero : index=0 := by rw [count] at bound; omega
    subst index
    have pairEqual : compiled.commitmentAliases[0]! = pair := by
      simpa only [getElem!_pos compiled.commitmentAliases 0 bound] using equal
    rw [←pairEqual,certifiedSchedule_alias_source resolver graph compiled certificate,
      source_commitment_meaning resolver graph compiled trace inputs commitment size,newSource,nativeCommitment]
  · exact intended_steps_admit_primitives compiled graph reference.steps actual
      (sourceValues resolver inputs commitment) observed intended admitted
  · rw [complete_read_root trace.final compiled trace.complete 2 compiled.publicNullifier.1 trace.publicNullifierRead,
      source_prefix_meaning resolver graph compiled trace inputs commitment size constant 2 (by decide),
      nullifierSource,nativeNullifier]

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.complete_read_root
#print axioms TornadoProofs.Witness.Execution.schedule_source_parts
