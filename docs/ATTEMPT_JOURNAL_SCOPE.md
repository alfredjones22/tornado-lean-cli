# Native attempt journal scope

`Tornado/Runtime/AttemptJournal.lean` is a bounded, append-only intent journal for
one-note and batch operations. It does not enable a deposit, withdrawal,
recovery, signer, or network command.

## Durable record contract

- The caller supplies an existing trusted local directory and a fresh,
  unpredictable 128-bit attempt ID encoded as 32 lowercase hex characters.
  Record names are `<attemptId>.<sequence>.journal` beginning at sequence 0.
- `start` writes the immutable preparation record. `append` validates the
  transition against a fresh disk replay, then calls
  `ProtectedIO.createPrivate`. That binding uses exclusive `O_EXCL` creation,
  mode `0600`, descriptor-based path and file checks, file `fsync`, and parent
  directory `fsync`. A competing writer cannot replace a slot. If a create or
  subsequent reload fails, the caller receives an error and must reload; it
  must not assume the record was absent.
- Every replay lists names for that exact attempt, requires a contiguous
  sequence from 0, reads each file through `ProtectedIO.readPrivate`, requires
  canonical UTF-8 JSON with no extra or duplicate fields, and applies each
  action through the existing direct `Policy.stepAttempt` or batch
  `Policy.Batch.step`. An empty history, missing middle slot, malformed name,
  unsafe file, wrong version/kind/ID/sequence, or invalid transition is an
  error. The directory listing is only an index; it does not authorize a file
  read. The bounded history limit is 20 records. Exceeding it stops progress
  and requires manual recovery; no tail is silently dropped.
- Preparation binds a 32-byte operation hash and one direct nullifier or up to
  12 unique batch nullifiers. The sign record must repeat the reviewed hash;
  this module does not verify the signature or signed operation bytes. Each
  batch reservation names a selected unreserved nullifier. Exposure requires
  all reservations. Confirmation includes the signed hash, a receipt reference,
  success and event-match assertions, and exact matched nullifiers. These
  assertions are still caller supplied.

## Crash and retry rule

`expose` and `send` are **intent records**, written before the relevant
proof-bearing RPC or broadcast. A standalone `append .expose` can be used for
simulation-only exposure, but it cannot later be upgraded to a send, including
after restart. `armSubmission` writes both exposure and the single send intent
back to back before any network effect. A crash between those writes leaves an
exposed record that cannot be armed later. A crash after both writes leaves a
submitted record whose send allowance is already consumed, even if no packet
was sent. This deliberately favors safety over liveness: a crash can leave an
unsent operation that cannot be retried.

After an ambiguous simulation or send result, the caller must append `unknown`
and reconcile from authenticated chain evidence. An unknown attempt cannot be
signed, reserved, exposed, or sent again. Confirmation may be appended only
after the policy accepts the supplied evidence fields. The journal does not
authenticate a receipt, prove finality, or verify that the referenced receipt
matches the actual chain.

## Remaining boundaries

- The journal alone has no cross-attempt per-nullifier claim. The separate
  [NoteClaims wrapper](NOTE_CLAIMS_SCOPE.md) adds exclusive claims within one
  private local instance and tests concurrent attempts. Integrations of this
  generic journal must use that wrapper and bind its identifiers to the actual
  signed operation. Connected experimental withdrawal commands use a separate
  opaque status-file journal with its own focused tests.
- The caller must put the directory on a local filesystem with reliable file
  and directory `fsync`, keep the attempt ID stable across restarts, and keep
  every journal operation within this API. This is not a process lock or a
  tamper-evident log. Deleting an entire tail, modifying files as the same OS
  user, or losing the disk cannot be detected from these records alone.
- The journal stores hashes and nullifier identifiers, not raw notes, private
  keys, proofs, or signed operation bytes. It cannot reconstruct a signed
  payload for rebroadcast. The 20-record cap and absence of a chain authenticator
  limit this generic API. Its pure refinement theorems are not an end-to-end
  proof of the separate runnable send adapters.
