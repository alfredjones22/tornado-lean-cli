import TornadoProofs.WorkerEntropy

open Lean Elab Term Meta
elab "actualWorkerBlinding" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `Tornado.Cli.ProverWorker
    `Tornado.Cli.ProverWorker.blindingProgram)

set_option autoImplicit false

namespace TornadoProofs.WorkerEntropy

open Tornado.Runtime.WorkerProgram LeanCrypto.Probability.Rejection
open LeanCrypto.Sampling LeanCrypto.FixedBytes
variable {α β : Type} {mode : Mode}

theorem interpret_sampleLoop (replies : File → Option ByteArray) (draw : Program mode (Option α))
    (exhausted : Program mode α) (budget : Nat) :
    interpret replies (sampleLoop draw exhausted budget) =
      sampleLoop (interpret replies draw) (interpret replies exhausted) budget := by
  induction budget with
  | zero => rfl
  | succ budget ih =>
    simp only [sampleLoop]
    dsimp only [Bind.bind]
    rw [interpret_bind]
    congr 1
    funext choice
    cases choice with
    | none => exact ih
    | some value => rfl

theorem interpret_samplePairLoop (replies : File → Option ByteArray)
    (draw : Program mode (Option α)) (exhausted : Program mode α) (budget : Nat) :
    interpret replies (samplePairLoop draw exhausted budget) =
      samplePairLoop (interpret replies draw) (interpret replies exhausted) budget := by
  unfold samplePairLoop
  dsimp only [Bind.bind]
  rw [interpret_bind, interpret_sampleLoop]
  congr 1
  funext first
  rw [interpret_bind, interpret_sampleLoop]
  rfl

theorem related_sampleLoop {D : Nat} {relation : α → β → Prop}
    (leftDraw : DrawTree (Option α)) (rightDraw : DrawTree (Option β))
    (leftExhausted : DrawTree α) (rightExhausted : DrawTree β)
    (draws : Related D (Option.Rel relation) leftDraw rightDraw)
    (exhaustion : Related D relation leftExhausted rightExhausted) (budget : Nat) :
    Related D relation (sampleLoop leftDraw leftExhausted budget)
      (sampleLoop rightDraw rightExhausted budget) := by
  induction budget with
  | zero => exact exhaustion
  | succ budget ih =>
    change Related D relation (leftDraw.bind _) (rightDraw.bind _)
    apply related_bind draws
    intro first second matchOptions
    cases matchOptions with
    | none => exact ih
    | some related => exact .done _ _ related

theorem related_samplePairLoop {D : Nat} {relation : α → β → Prop}
    (leftDraw : DrawTree (Option α)) (rightDraw : DrawTree (Option β))
    (leftExhausted : DrawTree α) (rightExhausted : DrawTree β)
    (draws : Related D (Option.Rel relation) leftDraw rightDraw)
    (exhaustion : Related D relation leftExhausted rightExhausted) (budget : Nat) :
    Related D (fun first second => relation first.1 second.1 ∧ relation first.2 second.2)
      (samplePairLoop leftDraw leftExhausted budget) (samplePairLoop rightDraw rightExhausted budget) := by
  have loop := related_sampleLoop leftDraw rightDraw leftExhausted rightExhausted draws exhaustion budget
  change Related D _ ((sampleLoop leftDraw leftExhausted budget).bind _)
    ((sampleLoop rightDraw rightExhausted budget).bind _)
  apply related_bind loop
  intro r firstR relatedR
  apply related_bind loop
  intro s firstS relatedS
  exact .done _ _ ⟨relatedR, relatedS⟩

theorem option_scalar_relation (first : Option Scalar) (second : Option Nat)
    (equal : first.map Scalar.value = second) :
    Option.Rel (fun scalar value => scalar.value = value) first second := by
  cases first with
  | none => simp only [Option.map_none] at equal; subst second; exact .none
  | some scalar => simp only [Option.map_some] at equal; subst second; exact .some rfl

def candidateProgram : Program .prove (Option Scalar) := do
  liftExcept <| admitCandidate (← entropy32 rfl)

theorem worker_draw_related (replies : File → Option ByteArray) :
    Related (2 ^ 256) (Option.Rel (fun scalar value => scalar.value = value))
      (interpret replies candidateProgram)
      (.draw (fun value => .done (candidate LeanCrypto.bn254ScalarPrime value))) := by
  change Related _ _ (.draw _) (.draw _)
  apply Related.draw
  intro value bounded
  have width : (encode 32 value).size = 32 := encode_size 32 value
  have decoded : bigEndianNat (encode 32 value) = value := by
    rw [LeanCrypto.Probability.ByteEntropy.runtime_decoder]
    exact decode_encode 32 value (by simpa only [LeanCrypto.Probability.ByteEntropy.uint256_radix] using bounded)
  have classifier : admitCandidate (encode 32 value) = .ok (admitValue value) := by
    simp only [admitCandidate, width, if_pos, decoded]
  dsimp only [Program.bind]
  rw [interpret_lift, classifier]
  apply Related.done
  apply option_scalar_relation
  exact runtime_candidate_matches value

abbrev originalBlindingProgram : Program .prove (Scalar × Scalar) := actualWorkerBlinding

/-- Actual worker blinding, including its exact 512-attempt control flow,
is related to the same sequential scalar sampler on every full byte draw. -/
theorem actual_worker_sampling_related (replies : File → Option ByteArray) :
    Related (2 ^ 256) (fun first second => first.1.value = second.1 ∧ first.2.value = second.2)
      (interpret replies originalBlindingProgram)
      (pairSampler LeanCrypto.bn254ScalarPrime maxAttempts) := by
  change Related _ _ (interpret replies (samplePairLoop candidateProgram .fail maxAttempts)) _
  rw [interpret_samplePairLoop]
  exact related_samplePairLoop _ _ _ _ (worker_draw_related replies) .abort maxAttempts

/-- Every arbitrary output event has exactly the sampler's native count;
failed sampling remains observable. No success conditioning is used. -/
theorem actual_worker_sampling_counts (replies : File → Option ByteArray)
    (event : Option (Nat × Nat) → Nat) :
    DrawTree.count (2 ^ 256) (maxAttempts + maxAttempts)
      (interpret replies originalBlindingProgram)
      (fun result => event (result.map (fun pair => (pair.1.value, pair.2.value)))) =
        pairMass (2 ^ 256) LeanCrypto.bn254ScalarPrime maxAttempts event := by
  apply related_counts (actual_worker_sampling_related replies)
  · rfl
  · intro first second related
    simp only [Option.map_some]
    rw [related.1, related.2]

end TornadoProofs.WorkerEntropy

#print axioms TornadoProofs.WorkerEntropy.interpret_sampleLoop
#print axioms TornadoProofs.WorkerEntropy.interpret_samplePairLoop
#print axioms TornadoProofs.WorkerEntropy.related_sampleLoop
#print axioms TornadoProofs.WorkerEntropy.related_samplePairLoop
#print axioms TornadoProofs.WorkerEntropy.option_scalar_relation
#print axioms TornadoProofs.WorkerEntropy.worker_draw_related
#print axioms TornadoProofs.WorkerEntropy.actual_worker_sampling_related
#print axioms TornadoProofs.WorkerEntropy.actual_worker_sampling_counts
