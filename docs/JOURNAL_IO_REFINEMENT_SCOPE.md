# Journal replay and send-intent refinement

`AttemptJournal.load` applies the public pure `replayRecord` to each
protected, canonically decoded record in sequence, validating one file at a
time in the append-only format.
`replayRecord` checks attempt ID, kind, and exact next sequence before calling
the existing policy transition. `start`, `append`, and `armSubmission` still
reload from disk; the `ProtectedIO` C binding provides exclusive creation and
file and directory `fsync`.

[`JournalIORefinement.lean`](../Tornado/Spec/JournalIORefinement.lean) proves four
facts about this **actual replay step**:

- An accepted record has the selected attempt ID, kind, and next sequence.
- An accepted direct send had an exposed, matching signed/reserved candidate
  with no previous send, and leaves the send count at one.
- An accepted batch send had all selected notes reserved, matching
  reviewed/signed hash, no previous send, and leaves the send count at one.
- Two consecutive send records cannot both replay successfully for either
  attempt kind.

The theorems reuse the concrete `AttemptJournal.advance_*` proofs and the
policy transitions that `load` invokes. `#print axioms` reports only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`; there are no custom
axioms or proof placeholders.

[`test-journal-io-refinement.mjs`](../scripts/test-journal-io-refinement.mjs)
drives the compiled [test binary](../tests/JournalIORefinement.lean) with public
fixture hashes. It denies directory writes after preparation and checks that
failed arming leaves the recovered state reserved; races two processes to arm
the same attempt and requires exactly one winner; then checks that a recovered
submitted attempt cannot be armed again. A second attempt stops after the
exposure record to model a crash between exposure and send; replay keeps it
exposed and rejects later arming. The permission-denial case is skipped when
the test runner is root, because root can bypass directory mode bits. The
journal and per-note-claim suites cover the corresponding replay and claim gates.

These tests exercise ordinary write denial, exclusive-create races, and
process restart. They do not inject power loss during `fsync`, prove OS
durability, defend against a same-user file rewrite/deletion, or show that a
network request happened only after a durable intent. The journal stores a
caller-supplied hash, not signed bytes, and its confirmation fields are
caller-supplied. Connected experimental commands use separate concrete
deposit/recovery/withdrawal journals; this generic replay proof does not
establish their whole IO trace. It does not prove the runnable commands' exact
signed-byte/review bindings, reservation/exposure order, handling of uncertain
outcomes or receipt/event gates. Those properties have focused runtime checks
and fault tests under the documented OS and chain-evidence assumptions.
