import TornadoProofs.PipelineComposition

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TornadoProofs.WorkerOutput

open Tornado.Protocol Tornado.Runtime.WorkerProgram
open Tornado.Protocol.ProverWorkerWire
open TornadoProofs.PipelineComposition TornadoProofs.ProofPrivacy
open TornadoProofs.WorkerEntropy
open LeanCrypto.Sampling LeanCrypto.Probability.Rejection
attribute [local instance] Classical.propDecidable

/-- The actual request-bound wire validator remains inside this observer. -/
def requestObservation (request : Request) : Option (ByteArray × Array Nat) → Option Result
  | none => none
  | some (bytes, signals) =>
    let result : Result := ⟨request.hash, bytes, signals⟩
    match result.validateFor request with
    | .error _ => none
    | .ok _ => some result

theorem finishProof_observation (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (r s : Nat) (request : Request) :
    (Tornado.Cli.ProverWorker.finishProof assets withdrawal r s request).toOption =
      requestObservation request (publicObservation assets withdrawal r s) := by
  unfold Tornado.Cli.ProverWorker.finishProof publicObservation
  cases generated : ClassicProofPipeline.prove assets withdrawal r s with
  | error message => rfl
  | ok proof =>
    simp only [Except.toOption, Option.map_some, requestObservation]
    cases checked : (Result.mk request.hash proof.bytes proof.signals).validateFor request <;> rfl

theorem finishProof_eq_native (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (context : Context)
    (source : ExecutionSource assets withdrawal context) (request : Request) (r s : Scalar) :
    (Tornado.Cli.ProverWorker.finishProof assets withdrawal r.value s.value request).toOption =
      requestObservation request (context.native (some (r.value, s.value))) := by
  rw [finishProof_observation, pipeline_observation assets withdrawal context source
    r.value s.value r.positive s.positive r.canonical s.canonical]

/-- Source tail after the already-admitted note/request/public-asset reads. -/
def actualTail (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (request : Request) : Program .prove Result :=
  originalBlindingProgram.bind (fun pair => liftExcept <|
    Tornado.Cli.ProverWorker.finishProof assets withdrawal pair.1.value pair.2.value request)

def resultTree : Option Result → DrawTree Result
  | none => .abort
  | some result => .done result

theorem resultTree_lift (replies : File → Option ByteArray) (value : Except String Result) :
    interpret replies (liftExcept value : Program .prove Result) = resultTree value.toOption := by
  cases value <;> rfl

def modelTail (context : Context) (request : Request) : DrawTree Result :=
  (pairSampler LeanCrypto.bn254ScalarPrime maxAttempts).bind (fun pair =>
    resultTree (requestObservation request (context.native (some pair))))

/-- The actual original worker tail, including request validation failures,
is bisimilar to the proved sampler followed by the proved native observer. -/
theorem actual_tail_related (replies : File → Option ByteArray)
    (assets : ClassicProofPipeline.PinnedAssets) (withdrawal : TornadoWitness.WithdrawalInput)
    (context : Context) (source : ExecutionSource assets withdrawal context) (request : Request) :
    Related (2 ^ 256) Eq (interpret replies (actualTail assets withdrawal request))
      (modelTail context request) := by
  unfold actualTail modelTail
  rw [interpret_bind]
  apply related_bind (actual_worker_sampling_related replies)
  intro pair nativePair relation
  rw [resultTree_lift, finishProof_eq_native assets withdrawal context source request pair.1 pair.2]
  have equal : (pair.1.value, pair.2.value) = nativePair := by
    exact Prod.ext relation.1 relation.2
  rw [equal]
  cases requestObservation request (context.native (some nativePair)) with
  | none => exact .abort
  | some result => exact .done result result rfl

/-- Entire terminal payload, fixed error diagnostic and exit status are
common deterministic post-processing. Physical partial writes are excluded. -/
def terminalObservation (request : Request) (result : Option Result) : String × String × UInt32 :=
  let terminal := terminal (result.map (Response.proof request))
  (terminal.stdout, terminal.stderr, terminal.exitCode)

theorem actual_tail_counts (replies : File → Option ByteArray)
    (assets : ClassicProofPipeline.PinnedAssets) (withdrawal : TornadoWitness.WithdrawalInput)
    (context : Context) (source : ExecutionSource assets withdrawal context) (request : Request)
    (event : Option Result → Nat) :
    DrawTree.count (2 ^ 256) (maxAttempts + maxAttempts)
      (interpret replies (actualTail assets withdrawal request)) event =
        pairMass (2 ^ 256) LeanCrypto.bn254ScalarPrime maxAttempts (fun masks =>
          event (masks.bind (fun pair => requestObservation request (context.native (some pair))))) := by
  have first := related_counts (actual_tail_related replies assets withdrawal context source request)
    (maxAttempts + maxAttempts) event event rfl (fun a b equal => congrArg (fun result => event (some result)) equal)
  rw [first]
  unfold modelTail pairMass
  let next := fun pair : Nat × Nat => resultTree (requestObservation request (context.native (some pair)))
  have bounded : ∀ pair, DrawTree.Bounded 0 (next pair) := by
    intro pair
    unfold next
    cases requestObservation request (context.native (some pair)) <;> trivial
  have equation := DrawTree.count_bind (2 ^ 256) (maxAttempts + maxAttempts) 0
    (pairSampler LeanCrypto.bn254ScalarPrime maxAttempts) next
    (pairSampler_bounded _ _) bounded event
  simp only [Nat.add_zero] at equation
  rw [equation]
  apply DrawTree.count_congr
  intro masks
  cases masks with
  | none => simp only [Option.bind_none, Nat.pow_zero, Nat.one_mul]
  | some pair =>
    simp only [Option.bind_some]
    dsimp only [next]
    cases requestObservation request (context.native (some pair)) <;>
      simp only [resultTree, DrawTree.count, Nat.pow_zero, Nat.one_mul]

noncomputable def probability (replies : File → Option ByteArray)
    (assets : ClassicProofPipeline.PinnedAssets) (withdrawal : TornadoWitness.WithdrawalInput)
    (request : Request) (event : String × String × UInt32 → Prop) : ℚ :=
  (DrawTree.count (2 ^ 256) (maxAttempts + maxAttempts)
    (interpret replies (actualTail assets withdrawal request))
    (fun result => if event (terminalObservation request result) then 1 else 0) : ℚ) /
      (2 ^ 256 : ℚ) ^ (maxAttempts + maxAttempts)

theorem probability_eq_context (replies : File → Option ByteArray)
    (assets : ClassicProofPipeline.PinnedAssets) (withdrawal : TornadoWitness.WithdrawalInput)
    (context : Context) (source : ExecutionSource assets withdrawal context) (request : Request)
    (event : String × String × UInt32 → Prop) :
    probability replies assets withdrawal request event =
      context.probability (fun payload => event (terminalObservation request
        (requestObservation request payload))) (2 ^ 256) maxAttempts := by
  have counts : DrawTree.count (2 ^ 256) (maxAttempts + maxAttempts)
      (interpret replies (actualTail assets withdrawal request))
      (fun result => if event (terminalObservation request result) then 1 else 0) =
        pairMass (2 ^ 256) LeanCrypto.bn254ScalarPrime maxAttempts
          (context.event (fun payload => event (terminalObservation request (requestObservation request payload)))) := by
    rw [actual_tail_counts replies assets withdrawal context source request]
    unfold pairMass
    apply DrawTree.count_congr
    intro masks
    cases masks <;> rfl
  unfold probability Context.probability
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact congrArg (fun count : Nat => (count : ℚ) / (2 ^ 256 : ℚ) ^ (maxAttempts + maxAttempts)) counts

/-- Quantified statistical privacy of the ORIGINAL worker proof tail's
stdout, stderr and exit-status fields. This includes all terminal wire
checks and rejection/exhaustion outcomes. Original source admission,
honest setup, IID full-width draws and physical IO trust remain explicit. -/
theorem actual_worker_tail_privacy (replies : File → Option ByteArray)
    (assetsFirst assetsSecond : ClassicProofPipeline.PinnedAssets)
    (withdrawalFirst withdrawalSecond : TornadoWitness.WithdrawalInput)
    (first second : Context)
    (sourceFirst : ExecutionSource assetsFirst withdrawalFirst first)
    (sourceSecond : ExecutionSource assetsSecond withdrawalSecond second)
    (request : Request) (sameSetup : first.setup = second.setup)
    (sameSignals : first.signals = second.signals) (event : String × String × UInt32 → Prop) :
    |probability replies assetsFirst withdrawalFirst request event -
      probability replies assetsSecond withdrawalSecond request event| ≤ (1 : ℚ) / 2 ^ 251 := by
  rw [probability_eq_context replies assetsFirst withdrawalFirst first sourceFirst request event,
    probability_eq_context replies assetsSecond withdrawalSecond second sourceSecond request event]
  exact actual_observation_bound_bits first second sameSetup sameSignals _ _ _ (by decide)

end TornadoProofs.WorkerOutput

#print axioms TornadoProofs.WorkerOutput.finishProof_observation
#print axioms TornadoProofs.WorkerOutput.finishProof_eq_native
#print axioms TornadoProofs.WorkerOutput.resultTree_lift
#print axioms TornadoProofs.WorkerOutput.actual_tail_related

#print axioms TornadoProofs.WorkerOutput.actual_tail_counts
#print axioms TornadoProofs.WorkerOutput.probability_eq_context
#print axioms TornadoProofs.WorkerOutput.actual_worker_tail_privacy
