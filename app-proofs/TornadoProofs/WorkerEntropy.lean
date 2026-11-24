import Tornado.Cli.ProverWorker
import LeanCryptoProofs.SamplerSupport

set_option autoImplicit false

namespace TornadoProofs.WorkerEntropy

open Tornado.Runtime.WorkerProgram LeanCrypto.Probability.Rejection
open LeanCrypto.Sampling LeanCrypto.FixedBytes

variable {α β γ δ : Type} {mode : Mode}

/-- Pure finite-byte interpretation of the ORIGINAL restricted effect tree.
Reads are fixed replies (possibly failed), and one draw denotes one actual
32-byte encoding. The native IO interpreter/OS coupling remains explicit. -/
def interpret (replies : File → Option ByteArray) : Program mode α → DrawTree α
  | .pure value => .done value
  | .fail => .abort
  | .read file _ next =>
    match replies file with
    | none => .abort
    | some bytes => interpret replies (next bytes)
  | .entropy32 _ next => .draw (fun value => interpret replies (next (encode 32 value)))

theorem interpret_bind (replies : File → Option ByteArray) (program : Program mode α)
    (next : α → Program mode β) :
    interpret replies (program.bind next) = (interpret replies program).bind
      (fun value => interpret replies (next value)) := by
  induction program with
  | pure value => rfl
  | fail => rfl
  | read file allowed continuation ih =>
    dsimp only [Program.bind, interpret]
    cases reply : replies file with
    | none => simp only [interpret, reply, DrawTree.bind]
    | some bytes => simpa only [interpret, reply] using ih bytes
  | entropy32 allowed continuation ih =>
    simp only [Program.bind, interpret, DrawTree.bind]
    congr 1
    funext value
    exact ih _

theorem interpret_lift (replies : File → Option ByteArray) (value : Except String α) :
    interpret replies (liftExcept value : Program mode α) =
      match value with | .ok result => .done result | .error _ => .abort := by
  cases value <;> rfl

/-- Bisimulation only on the admitted finite draw alphabet. Values outside
that alphabet do not need an artificial correspondence. -/
inductive Related (D : Nat) (relation : α → β → Prop) : DrawTree α → DrawTree β → Prop where
  | done (first : α) (second : β) : relation first second → Related D relation (.done first) (.done second)
  | abort : Related D relation .abort .abort
  | draw (first : Nat → DrawTree α) (second : Nat → DrawTree β) :
      (∀ value, value < D → Related D relation (first value) (second value)) →
        Related D relation (.draw first) (.draw second)

theorem related_counts {D : Nat} {relation : α → β → Prop} {first : DrawTree α} {second : DrawTree β}
    (related : Related D relation first second) (budget : Nat)
    (firstEvent : Option α → Nat) (secondEvent : Option β → Nat)
    (failures : firstEvent none = secondEvent none)
    (successes : ∀ a b, relation a b → firstEvent (some a) = secondEvent (some b)) :
    DrawTree.count D budget first firstEvent = DrawTree.count D budget second secondEvent := by
  induction budget generalizing first second with
  | zero =>
    cases related with
    | done a b equal => simp only [DrawTree.count, successes a b equal]
    | abort => simp only [DrawTree.count, failures]
    | draw => rfl
  | succ budget ih =>
    cases related with
    | done a b equal => simp only [DrawTree.count, successes a b equal]
    | abort => simp only [DrawTree.count, failures]
    | draw first second branches =>
      simp only [DrawTree.count]
      apply sumTo_congr
      intro value bounded
      exact ih (branches value bounded)

theorem related_bind {D : Nat} {relation : α → β → Prop} {finalRelation : γ → δ → Prop}
    {first : DrawTree α} {second : DrawTree β} (related : Related D relation first second)
    (leftNext : α → DrawTree γ) (rightNext : β → DrawTree δ)
    (continuations : ∀ a b, relation a b → Related D finalRelation (leftNext a) (rightNext b)) :
    Related D finalRelation (first.bind leftNext) (second.bind rightNext) := by
  induction related with
  | done a b equal => exact continuations a b equal
  | abort => exact .abort
  | draw first second branches ih =>
    exact .draw _ _ (fun value bounded => ih value bounded)

end TornadoProofs.WorkerEntropy

#print axioms TornadoProofs.WorkerEntropy.interpret_bind
#print axioms TornadoProofs.WorkerEntropy.interpret_lift
#print axioms TornadoProofs.WorkerEntropy.related_counts
#print axioms TornadoProofs.WorkerEntropy.related_bind
