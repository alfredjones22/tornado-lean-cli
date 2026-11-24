import TornadoProofs.WorkerOutput

open Lean Elab Term Meta
elab "originalWorkerPrivate" name:ident : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `Tornado.Cli.ProverWorker name.getId)

set_option autoImplicit false
namespace TornadoProofs.WorkerPrefix
open Tornado.Protocol Tornado.Runtime.WorkerProgram Tornado.Protocol.ProverWorkerWire
open TornadoProofs.WorkerOutput TornadoProofs.WorkerEntropy
open LeanCrypto.Probability.Rejection
attribute [local instance] Classical.propDecidable

variable {α β γ : Type} {mode : Mode}

theorem source_bind_assoc (program : Program mode α) (next : α → Program mode β)
    (last : β → Program mode γ) :
    (program.bind next).bind last = program.bind (fun value => (next value).bind last) := by
  induction program with
  | pure value => rfl
  | fail => rfl
  | read file allowed continuation ih =>
    simp only [Program.bind]
    congr 1
    funext bytes
    exact ih bytes
  | entropy32 allowed continuation ih =>
    simp only [Program.bind]
    congr 1
    funext bytes
    exact ih bytes

theorem source_bind_pure (program : Program mode α) : program.bind Program.pure = program := by
  induction program with
  | pure value => rfl
  | fail => rfl
  | read file allowed continuation ih =>
    simp only [Program.bind]
    congr 1
    funext bytes
    exact ih bytes
  | entropy32 allowed continuation ih =>
    simp only [Program.bind]
    congr 1
    funext bytes
    exact ih bytes

/-- Exact original source prefix through public asset admission, selected note,
request binding and original input preparation, before the first entropy draw. -/
def prefixProgram (noteIndex : Option String) (request : Request) :
    Program .prove (ClassicProofPipeline.PinnedAssets × TornadoWitness.WithdrawalInput) := do
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
  let path : Tornado.Crypto.MimcProof := ⟨request.leafIndex, request.root, request.siblings, request.pathIndices⟩
  let withdrawal : TornadoWitness.WithdrawalInput := {
    note, proof := path, expectedRoot := request.root, recipient := request.recipient,
    relayer := request.relayer, fee := request.fee, refund := request.refund }
  let _ ← liftExcept <| TornadoWitness.prepareInputPrefix withdrawal
  return (assets, withdrawal)

theorem original_proofProgram_factor (noteIndex : Option String) (request : Request) :
    Tornado.Cli.ProverWorker.proofProgram noteIndex request =
      (prefixProgram noteIndex request).bind (fun pair => actualTail pair.1 pair.2 request) := by
  unfold Tornado.Cli.ProverWorker.proofProgram prefixProgram actualTail
  cases Tornado.Domain.chainFromNat request.chainId <;>
    simp only [Bind.bind, source_bind_assoc, Program.bind, pure]

theorem original_proofProgram_after_admission (noteIndex : Option String) (request : Request)
    (replies : File → Option ByteArray) (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput)
    (admitted : interpret replies (prefixProgram noteIndex request) = .done (assets, withdrawal)) :
    interpret replies (Tornado.Cli.ProverWorker.proofProgram noteIndex request) =
      interpret replies (actualTail assets withdrawal request) := by
  rw [original_proofProgram_factor, interpret_bind, admitted]
  rfl

noncomputable def fullProbability (replies : File → Option ByteArray)
    (noteIndex : Option String) (request : Request) (event : String × String × UInt32 → Prop) : ℚ :=
  (DrawTree.count (2^256) (LeanCrypto.Sampling.maxAttempts+LeanCrypto.Sampling.maxAttempts)
    (interpret replies (Tornado.Cli.ProverWorker.proofProgram noteIndex request))
    (fun result => if event (terminalObservation request result) then 1 else 0) : ℚ) /
      (2^256 : ℚ)^(LeanCrypto.Sampling.maxAttempts+LeanCrypto.Sampling.maxAttempts)

theorem fullProbability_after_admission (noteIndex : Option String) (request : Request)
    (replies : File → Option ByteArray) (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput)
    (admitted : interpret replies (prefixProgram noteIndex request) = .done (assets, withdrawal))
    (event : String × String × UInt32 → Prop) :
    fullProbability replies noteIndex request event =
      probability replies assets withdrawal request event := by
  unfold fullProbability probability
  rw [original_proofProgram_after_admission noteIndex request replies assets withdrawal admitted]

/-- The ORIGINAL complete proofProgram, under explicit original admission,
has the same output privacy bound; its file replies may contain different
valid private notes. There is no success conditioning after admission. -/
theorem original_worker_output_privacy
    (firstReplies secondReplies : File → Option ByteArray)
    (firstIndex secondIndex : Option String) (request : Request)
    (firstAssets secondAssets : ClassicProofPipeline.PinnedAssets)
    (firstWithdrawal secondWithdrawal : TornadoWitness.WithdrawalInput)
    (firstAdmission : interpret firstReplies (prefixProgram firstIndex request) =
      .done (firstAssets, firstWithdrawal))
    (secondAdmission : interpret secondReplies (prefixProgram secondIndex request) =
      .done (secondAssets, secondWithdrawal))
    (first second : TornadoProofs.ProofPrivacy.Context)
    (firstSource : TornadoProofs.PipelineComposition.ExecutionSource firstAssets firstWithdrawal first)
    (secondSource : TornadoProofs.PipelineComposition.ExecutionSource secondAssets secondWithdrawal second)
    (sameSetup : first.setup = second.setup) (sameSignals : first.signals = second.signals)
    (event : String × String × UInt32 → Prop) :
    |fullProbability firstReplies firstIndex request event -
      fullProbability secondReplies secondIndex request event| ≤ (1 : ℚ) / 2^251 := by
  rw [fullProbability_after_admission firstIndex request firstReplies firstAssets firstWithdrawal firstAdmission,
    fullProbability_after_admission secondIndex request secondReplies secondAssets secondWithdrawal secondAdmission,
    probability_eq_context firstReplies firstAssets firstWithdrawal first firstSource request,
    probability_eq_context secondReplies secondAssets secondWithdrawal second secondSource request]
  exact TornadoProofs.ProofPrivacy.actual_observation_bound_bits first second sameSetup sameSignals _ _ _ (by decide)

end TornadoProofs.WorkerPrefix
#print axioms TornadoProofs.WorkerPrefix.source_bind_assoc
#print axioms TornadoProofs.WorkerPrefix.source_bind_pure
#print axioms TornadoProofs.WorkerPrefix.original_proofProgram_factor
#print axioms TornadoProofs.WorkerPrefix.original_proofProgram_after_admission

#print axioms TornadoProofs.WorkerPrefix.fullProbability_after_admission
#print axioms TornadoProofs.WorkerPrefix.original_worker_output_privacy
