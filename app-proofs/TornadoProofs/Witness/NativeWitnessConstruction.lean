import TornadoProofs.Witness.PipelineWitness
import TornadoProofs.Witness.InputInverse
import TornadoProofs.Witness.ReferenceProgramMeaning

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol TornadoWitness
open TornadoProofs.Witness.Execution

/-- Independent note/path facts and the actual public asset certificate
construct the original full native witness. The native reference-program
meaning is proved here, rather than required from the caller. -/
theorem native_construct_original_witness (assets : ClassicProofPipeline.PinnedAssets)
    (input : WithdrawalInput) (source : ValidWithdrawal input) :
    Nonempty (ConstructedWitness assets input) := by
  apply construct_original_witness assets input source
  intro resolver valid
  exact PedersenReference.referenceMeaning_construct resolver assets.graph.graph input source valid
    assets.publicWitness.pedersenBases

/-- Every input prefix admitted by the actual original validator belongs to
the independent source domain and has a constructively certified witness. -/
theorem native_construct_accepted_source (assets : ClassicProofPipeline.PinnedAssets)
    (input : WithdrawalInput) (inputs : Array Nat)
    (prepared : prepareInputPrefix input = .ok inputs) :
    Nonempty (ConstructedWitness assets input) :=
  native_construct_original_witness assets input (prepareInputPrefix_source input inputs prepared).1

/-- No caller-supplied VM, R1CS or final Groth16 success is assumed. The
original accepted prefix produces a complete canonical witness, with exact
reviewed public signals, passing every authenticated circuit equation. -/
theorem native_construct_accepted_witness (assets : ClassicProofPipeline.PinnedAssets)
    (input : WithdrawalInput) (inputs : Array Nat)
    (prepared : prepareInputPrefix input = .ok inputs) :
    ∃ witness,
      WitnessVM.generateCheckedWitness assets.graph assets.circuit inputs input.note.commitment = .ok witness ∧
      witness.size = 28300 ∧ Primitive.Bounded witness ∧
      witness.extract 1 7 = (ClassicProofPipeline.ReviewedPublic.ofWithdrawal input).signals ∧
      Groth16R1CS.checkCircuit assets.circuit.circuit witness = .ok 28275 := by
  obtain ⟨source⟩ := native_construct_accepted_source assets input inputs prepared
  have original := (prepareInputPrefix_source input inputs prepared).2
  refine ⟨source.witness,?_,source.shape,source.canonical,source.witnessSignals,source.checked⟩
  simpa only [original] using source.witnessBuilt

/-- The original worker reference receives its witness evidence solely from
the constructed source artifact. Actual key decoding/H computation and the
context's protocol setup/QAP relations remain separate explicit evidence. -/
theorem native_worker_reference_from_accepted (assets : ClassicProofPipeline.PinnedAssets)
    (input : WithdrawalInput) (inputs : Array Nat)
    (prepared : prepareInputPrefix input = .ok inputs) :
    ∃ source : ConstructedWitness assets input,
      ∀ (context : TornadoProofs.ProofPrivacy.Context) (decoded : ProvingKey.ParsedKey),
        context.witness = source.witness →
        ProvingKey.decodeFullKey assets.key = .ok decoded →
        FrFFT.calculateH decoded.header.domainSize context.witness decoded.polsA decoded.polsB = .ok context.h →
        context.key = Groth16MSM.QueryKey.fromParsed decoded →
        decoded.header.nVars = 28300 → decoded.header.nPublic = 6 →
        decoded.header.domainSize = 32768 → decoded.hExps.size = 32767 →
        Nonempty (TornadoProofs.PipelineComposition.ExecutionSource assets input context) := by
  obtain ⟨source⟩ := native_construct_accepted_source assets input inputs prepared
  refine ⟨source,?_⟩
  intro context decoded witness key h query variableCount publicCount domain count
  exact executionSource_from_constructed assets input context source witness decoded key h query variableCount publicCount domain count

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.native_construct_original_witness
#print axioms TornadoProofs.Witness.Source.native_construct_accepted_source
#print axioms TornadoProofs.Witness.Source.native_construct_accepted_witness
#print axioms TornadoProofs.Witness.Source.native_worker_reference_from_accepted
