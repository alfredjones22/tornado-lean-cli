import TornadoProofs.Witness.NativeWitnessConstruction
import TornadoProofs.OutputSimulation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Source
open Tornado.Protocol TornadoWitness
open Tornado.Runtime.WorkerProgram Tornado.Protocol.ProverWorkerWire
open TornadoProofs.WorkerEntropy TornadoProofs.WorkerPrefix
open TornadoProofs.ProofPrivacy TornadoProofs.OutputSimulation
open LeanCrypto.Probability.Rejection

/-- A proof-only view of the original read/parse prefix. The equality below
binds this view to the actual prefix, whose input preparation is retained. -/
def prefixBeforePreparation (noteIndex : Option String) (request : Request) :
    Program .prove (ClassicProofPipeline.PinnedAssets × WithdrawalInput) := do
  liftExcept request.validate
  let some chain := Tornado.Domain.chainFromNat request.chainId | .fail
  let circuit ← read (.asset .circuit) rfl
  let key ← read (.asset .key) rfl
  let graph ← liftExcept <| (originalWorkerPrivate Tornado.Cli.ProverWorker.text)
    (← read (.asset .graph) rfl)
  let certificate ← read (.asset .witnessCertificate) rfl
  let assets ← liftExcept <| ClassicProofPipeline.loadBundled circuit key graph certificate
  let selected ← (originalWorkerPrivate Tornado.Cli.ProverWorker.selectedProgram) chain noteIndex
  let note ← liftExcept <| (originalWorkerPrivate Tornado.Cli.ProverWorker.noteForRequest) selected request
  let path : Tornado.Crypto.MimcProof := ⟨request.leafIndex,request.root,request.siblings,request.pathIndices⟩
  let withdrawal : WithdrawalInput := {
    note,proof:=path,expectedRoot:=request.root,recipient:=request.recipient,
    relayer:=request.relayer,fee:=request.fee,refund:=request.refund }
  return (assets,withdrawal)

theorem prefixProgram_preparation_factor (noteIndex : Option String) (request : Request) :
    prefixProgram noteIndex request = (prefixBeforePreparation noteIndex request).bind (fun pair => do
      let _ ← liftExcept (prepareInputPrefix pair.2)
      pure pair) := by
  unfold prefixProgram prefixBeforePreparation
  cases Tornado.Domain.chainFromNat request.chainId <;>
    simp only [Bind.bind,source_bind_assoc,Program.bind,pure]

theorem drawTree_bind_done {A B : Type} (tree : DrawTree A) (next : A → DrawTree B) (result : B)
    (returned : tree.bind next = .done result) :
    ∃ value,tree = .done value ∧ next value = .done result := by
  cases tree with
  | abort => cases returned
  | draw choices => cases returned
  | done value => exact ⟨value,rfl,returned⟩

/-- Successful ORIGINAL worker-prefix admission includes successful ORIGINAL
input validation; no separate source-acceptance hypothesis is introduced. -/
theorem prefix_admission_prepared (noteIndex : Option String) (request : Request)
    (replies : File → Option ByteArray) (assets : ClassicProofPipeline.PinnedAssets) (input : WithdrawalInput)
    (admission : interpret replies (prefixProgram noteIndex request) = .done (assets,input)) :
    ∃ inputs,prepareInputPrefix input = .ok inputs := by
  rw [prefixProgram_preparation_factor,interpret_bind] at admission
  obtain ⟨pair,_,checked⟩ := drawTree_bind_done _ _ (assets,input) admission
  change interpret replies
    ((Tornado.Runtime.WorkerProgram.liftExcept (prepareInputPrefix pair.2) :
      Program .prove (Array Nat)).bind (fun _ => .pure pair)) = .done (assets,input) at checked
  rw [interpret_bind,interpret_lift] at checked
  cases prepared : prepareInputPrefix pair.2 with
  | error message => simp only [prepared,DrawTree.bind] at checked; cases checked
  | ok inputs =>
    have equal : pair = (assets,input) := by
      simpa only [prepared,DrawTree.bind,interpret,DrawTree.done.injEq] using checked
    cases equal
    exact ⟨inputs,prepared⟩

/-- A single witness-free terminal reference for the ORIGINAL complete worker.
The actual source prefix constructs the witness artifact. The remaining
context, key/H computations and setup/QAP relations stay explicit. Entropy
uses the stated finite IID-byte model; OS/timing/partial-output coupling is
not asserted by this theorem. -/
theorem native_original_worker_reference_bound (noteIndex : Option String) (request : Request)
    (replies : File → Option ByteArray) (assets : ClassicProofPipeline.PinnedAssets) (input : WithdrawalInput)
    (admission : interpret replies (prefixProgram noteIndex request) = .done (assets,input)) :
    ∃ source : ConstructedWitness assets input,
      ∀ (context : Context) (decoded : ProvingKey.ParsedKey),
        context.witness = source.witness →
        ProvingKey.decodeFullKey assets.key = .ok decoded →
        FrFFT.calculateH decoded.header.domainSize context.witness decoded.polsA decoded.polsB = .ok context.h →
        context.key = Groth16MSM.QueryKey.fromParsed decoded →
        decoded.header.nVars = 28300 → decoded.header.nPublic = 6 →
        decoded.header.domainSize = 32768 → decoded.hExps.size = 32767 →
        ∀ event : String × String × UInt32 → Prop,
          |fullProbability replies noteIndex request event -
            referenceTerminalProbability context.setup context.signals request event| ≤ (1 : ℚ)/2^251 := by
  obtain ⟨inputs,prepared⟩ := prefix_admission_prepared noteIndex request replies assets input admission
  obtain ⟨source⟩ := native_construct_accepted_source assets input inputs prepared
  refine ⟨source,?_⟩
  intro context decoded witness key h query variableCount publicCount domain count event
  obtain ⟨original⟩ := executionSource_from_constructed assets input context source witness decoded key h query
    variableCount publicCount domain count
  exact original_worker_reference_bound noteIndex request replies assets input admission context original event

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.prefixProgram_preparation_factor
#print axioms TornadoProofs.Witness.Source.drawTree_bind_done
#print axioms TornadoProofs.Witness.Source.prefix_admission_prepared
#print axioms TornadoProofs.Witness.Source.native_original_worker_reference_bound
