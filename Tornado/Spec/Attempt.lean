import Tornado.Policy
import Tornado.Policy.Batch
import Tornado.Protocol.Events

/-!
An independent statement of the minimum one-note and batch fund-safety
properties. This file defines specifications and reachability only. The
refinement proofs over the native policy functions live in `Refinement.lean`.

The `reserve` and `reserveNote` actions are abstract assertions of durable
reservations. A real file adapter must establish those assertions before it
may call a transition that exposes a signed operation. Likewise, receipt and
log values are caller supplied; chain authenticity is outside these pure
definitions.
-/

namespace Tornado.Spec

/-- A run consists only of successful transitions from the default one-note
    state. The action history is retained to make the trace boundary explicit. -/
inductive DirectRun : List Tornado.Policy.AttemptAction → Tornado.Policy.Attempt → Prop where
  | initial : DirectRun [] {}
  | append {actions : List Tornado.Policy.AttemptAction}
      {before after : Tornado.Policy.Attempt}
      (prior : DirectRun actions before)
      (action : Tornado.Policy.AttemptAction)
      (transition : Tornado.Policy.stepAttempt before action = .ok after) :
      DirectRun (actions ++ [action]) after

/-- The batch run starts without selected notes or a prepared operation. -/
inductive BatchRun : List Tornado.Policy.Batch.Action → Tornado.Policy.Batch.Attempt → Prop where
  | initial : BatchRun [] {}
  | append {actions : List Tornado.Policy.Batch.Action}
      {before after : Tornado.Policy.Batch.Attempt}
      (prior : BatchRun actions before)
      (action : Tornado.Policy.Batch.Action)
      (transition : Tornado.Policy.Batch.step before action = .ok after) :
      BatchRun (actions ++ [action]) after

/-- An operation may be submitted at most once, even if its outcome becomes
    uncertain or it is later confirmed. -/
def AtMostOneSend (sends : Nat) : Prop := sends ≤ 1

/-- A reachable one-note candidate cannot have a signature before review;
    once a signature exists, its hash remains the reviewed hash. -/
def DirectReviewInvariant (state : Tornado.Policy.Attempt) : Prop :=
  (state.phase = .fresh → state.signedHash = none) ∧
  (state.signedHash.isSome → state.reviewedHash = state.signedHash)

/-- Before direct exposure, the reviewed, signed and reserved operation hashes
    must agree and the reservation must actually name an operation. -/
def DirectExposureSpec (state : Tornado.Policy.Attempt) : Prop :=
  ∃ hash : String,
    state.reviewedHash = some hash ∧
    state.signedHash = some hash ∧
    state.reservedHash = some hash

/-- Before batch exposure, each reviewed nullifier is reserved, and the
    reviewed hash is the signed hash. This says nothing about disk durability. -/
def BatchExposureSpec (state : Tornado.Policy.Batch.Attempt) : Prop :=
  state.selected ≠ [] ∧
  (∀ nullifier, nullifier ∈ state.selected → nullifier ∈ state.reserved) ∧
  ∃ hash : String,
    state.reviewedHash = some hash ∧ state.signedHash = some hash

/-- The empty batch has no selected notes; every later phase must retain the
    nonempty, unique selection admitted by `prepare`. -/
def BatchSelectionInvariant (state : Tornado.Policy.Batch.Attempt) : Prop :=
  (state.phase = .fresh → state.selected = []) ∧
  (state.phase ≠ .fresh → Tornado.Policy.Batch.validSelection state.selected = true)

/-- These are independent field-level acceptance requirements for a direct
    receipt. The caller must prove the logs and receipt came from the intended
    chain and transaction before the result is treated as final. -/
def DirectConfirmationSpec (receiptSuccess : Bool)
    (logs : List Tornado.Protocol.Events.Log)
    (entry : Tornado.Protocol.Events.ExpectedEntry)
    (withdrawal : Tornado.Protocol.Events.ExpectedWithdrawal) : Prop :=
  receiptSuccess = true ∧
  Tornado.Protocol.Events.uniqueEntryResult logs entry = some true ∧
  Tornado.Protocol.Events.hasWithdrawal logs withdrawal = true

/-- Batch confirmation requires evidence for every selected withdrawal. -/
def BatchConfirmationSpec (receiptSuccess : Bool)
    (logs : List Tornado.Protocol.Events.Log)
    (entry : Tornado.Protocol.Events.ExpectedEntry)
    (withdrawals : List Tornado.Protocol.Events.ExpectedWithdrawal) : Prop :=
  receiptSuccess = true ∧
  Tornado.Protocol.Events.uniqueEntryResult logs entry = some true ∧
  withdrawals ≠ [] ∧
  (∀ withdrawal, withdrawal ∈ withdrawals →
    Tornado.Protocol.Events.hasWithdrawal logs withdrawal = true)

end Tornado.Spec
