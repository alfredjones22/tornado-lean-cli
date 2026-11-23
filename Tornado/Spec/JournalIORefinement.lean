import Tornado.Runtime.AttemptJournal

/-!
Facts about the *pure replay step called by* `AttemptJournal.load`. Disk reads,
exclusive creation, fsync, process crashes, and receipt authenticity remain
outside the Lean theorem boundary. Successful replay of a record is still a
useful executable precondition for the later IO path.
-/

namespace Tornado.Spec.JournalIORefinement

open Tornado.Runtime.AttemptJournal

/-- A decoded journal record cannot be replayed into a different attempt,
    kind, or sequence slot. This is the exact guard used by `load`. -/
theorem replay_success_metadata (before after : State) (record : Record)
    (accepted : replayRecord before record = .ok after) :
    record.attemptId = before.attemptId ∧
    record.kind = before.kind ∧ record.seq = before.nextSeq := by
  by_cases hg : record.attemptId = before.attemptId ∧
      record.kind = before.kind ∧ record.seq = before.nextSeq
  · exact hg
  · simp [replayRecord, hg] at accepted

/-- The actual disk replay step cannot accept a direct send unless the prior
    candidate was exposed with a matching reserved/signed hash and no send;
    the returned state consumes the single send slot. -/
theorem replay_direct_send_requires_reservation (before after : State)
    (record : Record) (kind : before.kind = .direct)
    (event : record.event = .send)
    (accepted : replayRecord before record = .ok after) :
    before.direct.phase = .exposed ∧
    before.direct.reservedHash = before.direct.signedHash ∧
    before.direct.reservedHash.isSome = true ∧
    before.direct.sends = 0 ∧
    after.direct.phase = .submitted ∧ after.direct.sends = 1 := by
  have metadata := replay_success_metadata before after record accepted
  have prior := advance_direct_send_requires_exposed before after kind (by
    simpa [replayRecord, metadata, event] using accepted)
  have consumed := advance_direct_send_consumes_slot before after kind (by
    simpa [replayRecord, metadata, event] using accepted)
  exact ⟨prior.1, prior.2.1, prior.2.2.1, prior.2.2.2, consumed.1, consumed.2⟩

/-- A batch send reconstructed from protected records requires every selected
    nullifier reserved and consumes the only send slot. -/
theorem replay_batch_send_requires_all_reservations (before after : State)
    (record : Record) (kind : before.kind = .batch)
    (event : record.event = .send)
    (accepted : replayRecord before record = .ok after) :
    (before.batch.phase == .exposed) = true ∧
    Tornado.Policy.Batch.allReserved before.batch = true ∧
    before.batch.reviewedHash = before.batch.signedHash ∧
    before.batch.signedHash.isSome = true ∧
    before.batch.sends = 0 ∧
    after.batch.phase = .submitted ∧ after.batch.sends = 1 := by
  have metadata := replay_success_metadata before after record accepted
  have prior := advance_batch_send_requires_reserved before after kind (by
    simpa [replayRecord, metadata, event] using accepted)
  have consumed := advance_batch_send_consumes_slot before after kind (by
    simpa [replayRecord, metadata, event] using accepted)
  exact ⟨prior.1, prior.2.1, prior.2.2.1, prior.2.2.2.1,
    prior.2.2.2.2, consumed.1, consumed.2⟩

/-- A second send record cannot be replayed immediately after a successful
    send, for either attempt kind. The OS must still ensure the two files
    actually existed and were read without tampering. -/
theorem replay_send_no_repeat (before after later : State)
    (first second : Record)
    (firstEvent : first.event = .send)
    (secondEvent : second.event = .send)
    (one : replayRecord before first = .ok after)
    (two : replayRecord after second = .ok later) : False := by
  have oneMeta := replay_success_metadata before after first one
  have twoMeta := replay_success_metadata after later second two
  cases hk : before.kind with
  | direct =>
      exact advance_direct_send_no_repeat before after later hk
        (by simpa [replayRecord, oneMeta, firstEvent] using one)
        (by simpa [replayRecord, twoMeta, secondEvent] using two)
  | batch =>
      exact advance_batch_send_no_repeat before after later hk
        (by simpa [replayRecord, oneMeta, firstEvent] using one)
        (by simpa [replayRecord, twoMeta, secondEvent] using two)

end Tornado.Spec.JournalIORefinement

#print axioms Tornado.Spec.JournalIORefinement.replay_success_metadata
#print axioms Tornado.Spec.JournalIORefinement.replay_direct_send_requires_reservation
#print axioms Tornado.Spec.JournalIORefinement.replay_batch_send_requires_all_reservations
#print axioms Tornado.Spec.JournalIORefinement.replay_send_no_repeat
