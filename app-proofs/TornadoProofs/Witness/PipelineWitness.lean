import TornadoProofs.Witness.ReferenceConstruction
import TornadoProofs.PipelineComposition

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol TornadoWitness
open TornadoProofs.Witness.Execution

/-- A proof-only source artifact constructed from the original note/path and
public assets. Its actual execution/check facts are conclusions of the source
construction theorem, not caller-supplied final-success assumptions. -/
structure ConstructedWitness (assets : ClassicProofPipeline.PinnedAssets) (input : WithdrawalInput) where
  private mk ::
  witness : Array Nat
  inputBuilt : prepareInputPrefix input=.ok (inputPrefix input)
  witnessBuilt : WitnessVM.generateCheckedWitness assets.graph assets.circuit (inputPrefix input)
    input.note.commitment=.ok witness
  inputSignals : (inputPrefix input).extract 1 7=(ClassicProofPipeline.ReviewedPublic.ofWithdrawal input).signals
  witnessSignals : witness.extract 1 7=(ClassicProofPipeline.ReviewedPublic.ofWithdrawal input).signals
  shape : witness.size=28300
  canonical : Primitive.Bounded witness
  checked : Groth16R1CS.checkCircuit assets.circuit.circuit witness=.ok 28275

theorem construct_original_witness (assets : ClassicProofPipeline.PinnedAssets) (input : WithdrawalInput)
    (source : ValidWithdrawal input)
    (native : ∀ resolver,WitnessSymbolic.tableValid resolver.nodes=true → ReferenceMeaning resolver assets.graph.graph input) :
    Nonempty (ConstructedWitness assets input) := by
  obtain ⟨witness,prepared,constructed,shape,canonical,signals,checked⟩ :=
    certified_witness_from_reference assets input source native
  exact ⟨⟨witness,prepared,constructed,inputPrefix_reviewed_signals input source,signals,shape,canonical,checked⟩⟩

/-- Adapter to the original worker privacy composition. The witness success
field is supplied solely by the constructive source artifact. Key parsing, H,
and the protocol's setup/point relations belong to their independent tracks. -/
theorem executionSource_from_constructed (assets : ClassicProofPipeline.PinnedAssets) (input : WithdrawalInput)
    (context : TornadoProofs.ProofPrivacy.Context) (source : ConstructedWitness assets input)
    (contextWitness : context.witness=source.witness) (decoded : ProvingKey.ParsedKey)
    (keyBuilt : ProvingKey.decodeFullKey assets.key=.ok decoded)
    (hBuilt : FrFFT.calculateH decoded.header.domainSize context.witness decoded.polsA decoded.polsB=.ok context.h)
    (queryKey : context.key=Groth16MSM.QueryKey.fromParsed decoded)
    (nVars : decoded.header.nVars=28300) (nPublic : decoded.header.nPublic=6)
    (domain : decoded.header.domainSize=32768) (hCount : decoded.hExps.size=32767) :
    Nonempty (TornadoProofs.PipelineComposition.ExecutionSource assets input context) := by
  refine ⟨⟨inputPrefix input,decoded,source.inputBuilt,source.inputSignals,?_,keyBuilt,hBuilt,
    queryKey,nVars,nPublic,domain,hCount,?_⟩⟩
  · simpa only [contextWitness] using source.witnessBuilt
  · unfold TornadoProofs.ProofPrivacy.Context.signals
    rw [contextWitness,queryKey]
    change source.witness.extract 1 (decoded.header.nPublic+1)=_
    simpa only [nPublic] using source.witnessSignals

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.construct_original_witness
#print axioms TornadoProofs.Witness.Source.executionSource_from_constructed
