import TornadoProofs.Witness.InputConstruction
import TornadoProofs.Witness.ScheduleSource
import TornadoProofs.Witness.WitnessPrefix

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.TornadoWitness
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.PedersenSchedule
open TornadoProofs.Witness.Execution

/-- The reusable group/window theorem interface: interpret the independently
compiled reference program on the original note bits and public native bases.
This arithmetic relation mentions neither VM acceptance nor an R1CS checker. -/
def ReferenceMeaning (resolver : Resolver) (graph : SelectedGraph) (input : WithdrawalInput) : Prop :=
  let values := sourceValues resolver (inputPrefix input) input.note.commitment
  ∀ reference,referenceSchedule resolver graph=.ok reference →
    StepsAdmitted values reference.steps ∧ values[reference.commitment.1]! = input.note.commitment ∧
      values[reference.nullifier.1]! = input.note.nullifierHash

theorem reference_to_graph_source (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (schedule : CertifiedSchedule resolver graph compiled)
    (input : WithdrawalInput) (source : ValidWithdrawal input) (native : ReferenceMeaning resolver graph input) :
    GraphSourceAdmitted graph compiled (sourceValues resolver (inputPrefix input) input.note.commitment) := by
  obtain ⟨reference,_,referenceBuilt,_,_⟩ := certifiedSchedule_accepted resolver graph compiled schedule
  obtain ⟨admitted,commitment,nullifier⟩ := native reference referenceBuilt
  have nullifierInput : (inputPrefix input)[2]! = input.note.nullifierHash := by
    rw [inputPrefix_header input 2 (by decide)]
    rfl
  have parts := schedule_source_parts resolver graph compiled trace schedule (inputPrefix input) input.note.commitment
    (valid_prefix_size input source) (valid_prefix_constant input) reference referenceBuilt admitted commitment
    (by simpa only [nullifierInput] using nullifier)
  have rootInput : (inputPrefix input)[1]! = input.proof.root := by
    rw [inputPrefix_header input 1 (by decide)]
    rfl
  have membership : nativePathPrefix Tornado.Crypto.mimcConstants (inputPrefix input) input.note.commitment 20 =
      .ok (inputPrefix input)[1]! := by simpa only [rootInput] using source.membership
  exact ⟨parts.aliases,
    source_bits_admitted resolver graph compiled trace (inputPrefix input) input.note.commitment
      (valid_prefix_size input source) (valid_prefix_constant input)
      (valid_prefix_bits input source).1 (valid_prefix_bits input source).2,
    parts.primitives,
    source_selectors_admitted resolver graph compiled trace (inputPrefix input) input.note.commitment
      (valid_prefix_size input source) (valid_prefix_constant input) (valid_prefix_binary input source),
    source_path_root resolver graph compiled trace (inputPrefix input) input.note.commitment
      (valid_prefix_size input source) (valid_prefix_constant input) (valid_prefix_canonical input source)
      (valid_commitment_canonical input source) (valid_prefix_binary input source) parts.aliases membership,
    parts.nullifier⟩

/-- Once the independent native group/window interpretation is supplied,
original note/path facts construct the real input prefix, complete native
witness, and all authenticated circuit checks. -/
theorem certified_witness_from_reference (assets : Tornado.Protocol.ClassicProofPipeline.PinnedAssets)
    (input : WithdrawalInput) (source : ValidWithdrawal input)
    (native : ∀ resolver,tableValid resolver.nodes=true → ReferenceMeaning resolver assets.graph.graph input) :
    ∃ witness,
      prepareInputPrefix input=.ok (inputPrefix input) ∧
      generateCheckedWitness assets.graph assets.circuit (inputPrefix input) input.note.commitment=.ok witness ∧
      witness.size=28300 ∧ Primitive.Bounded witness ∧
      witness.extract 1 7=(Tornado.Protocol.ClassicProofPipeline.ReviewedPublic.ofWithdrawal input).signals ∧
      Tornado.Protocol.Groth16R1CS.checkCircuit assets.circuit.circuit witness=.ok 28275 := by
  obtain ⟨data,compiled,system,variableCount,built,generated,checked,⟨schedule⟩⟩ :=
    certifiedPublic_schedule assets.graph.graph assets.circuit.circuit assets.publicWitness
  let resolver := Resolver.ofNodes data.nodes
  obtain ⟨trace⟩ := compileGraph_trace resolver assets.graph.graph compiled built
  have admitted := reference_to_graph_source resolver assets.graph.graph compiled trace schedule input source (native resolver trace.table)
  let values := sourceValues resolver (inputPrefix input) input.note.commitment
  let witness := witnessValues compiled.signalRoots values assets.graph.graph.nVars
  have constructed := generateCheckedWitness_source assets.graph assets.circuit resolver compiled system data.elimination
    variableCount built generated checked (inputPrefix input) input.note.commitment (valid_prefix_size input source)
    (valid_prefix_constant input) (valid_prefix_canonical input source) (valid_commitment_canonical input source) admitted
  refine ⟨witness,prepareInputPrefix_construct input source,constructed,?_,?_,?_,?_⟩
  · exact (witnessValues_size _ _ _).trans (graph_layout_dimensions assets.graph.graph trace.layout).2
  · intro value member
    exact witnessValues_canonical compiled.signalRoots values assets.graph.graph.nVars
      (sourceValues_bounded resolver (inputPrefix input) input.note.commitment trace.table
        (valid_prefix_canonical input source) (valid_commitment_canonical input source)) value
      (Array.mem_toList_iff.mp member)
  · exact (witnessValues_source_slice resolver assets.graph.graph compiled trace (inputPrefix input)
      input.note.commitment (valid_prefix_size input source) (valid_prefix_constant input)).trans
        (inputPrefix_reviewed_signals input source)
  · exact generateCheckedWitness_passes assets.graph assets.circuit (inputPrefix input) input.note.commitment witness constructed

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.reference_to_graph_source
#print axioms TornadoProofs.Witness.Source.certified_witness_from_reference
