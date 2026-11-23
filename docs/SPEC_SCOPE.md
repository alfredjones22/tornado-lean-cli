# Native CLI safety specification: current scope

`Tornado/Spec/Attempt.lean` states fund-safety requirements independently of
the policy transition code. `Tornado/Spec/Refinement.lean` proves that the
current native `Tornado.Policy` and `Tornado.Policy.Batch` transition functions
preserve or satisfy those requirements along traces starting from their empty
states. The proof module imports the *actual native definitions* that it
constrains; it does not model a separate imaginary CLI. Its 14 exported
theorems are kernel checked by pinned Lean 4.29.1. `#print axioms` reports only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` where used.

## What the specification says

- A successful one-note or batch trace records at most one send. A state that
  already records one send cannot pass either native send transition again.
- Once a one-note signature exists in a reachable state, it remains bound to
  the reviewed hash. A successful exposure in such a trace requires one
  identical reviewed, signed, and reserved hash.
- Every nonfresh batch state retains the nonempty, distinct, at-most-12-note
  selection admitted by `prepare`. A successful batch exposure in a reachable
  trace requires every selected note to be present in the reservation list
  and the signed hash to equal the reviewed hash.
- A confirmation through the native event-to-policy bridge extends a
  successful trace only with an exact decoded EntryPoint event and pool
  Withdrawal evidence. For a batch, every selected withdrawal must match,
  and the bridge checks the operation hash and selected nullifier list against
  the policy state. The generic `DirectRun` and `BatchRun` relations also admit
  raw `.confirm` actions, so exact decoded evidence is guaranteed only for
  the explicitly bridged confirmation theorem. A raw confirmation action does
  not carry that guarantee.

`tests/SpecRefinement.lean` constructs concrete one-note and two-note batch
traces from the initial states through reservation and exposure, checking that
the theorem premises are reachable. It also exercises first-send, second-send,
and unknown-outcome retry behavior. These are executable sanity checks; the
theorems provide the universal statement for the pure transition functions.

## Abstract effect trace

`Tornado/Spec/Effects.lean` adds executable **pure command-driver skeletons**
around the one-note and batch policies. Each records `durableReservation`,
`signedExposure`, `send`, `uncertain`, and `authenticatedConfirmation` events
in order. It accepts an abstract `DurableAck` only when its `durable` bit and
signed operation hash match the policy state. The batch driver also requires
the acknowledged nullifier to be selected, and checks that **every** selected
note has an acknowledgment before it exposes or sends the signed operation.
A receipt-confirmation action
requires an injected `authenticate` function to accept the receipt, the
receipt's chain ID and transaction hash to match the configured chain, and
the strict event-to-policy bridge to accept the pool and EntryPoint logs.

`Tornado/Spec/EffectRefinement.lean` proves 16 properties of these *actual
pure driver functions*: successful one-note exposure requires a matching acknowledgment;
each accepted transition preserves the reservation-log invariant; every
reachable acknowledgment has a prior durable-reservation event; exposure
appends its event; thus a successful exposure in a reachable run has the
matching durable-reservation event in the **earlier** log; confirmation
requires a positive authenticator result and exact decoded events; and an
uncertain candidate rejects new review, signing, reservation, exposure, and
send. For batch, accepted transitions preserve both the reservation-log
invariant and the selection-to-configuration invariant. A reachable batch has
either made no selection or has selected exactly the configured nullifiers.
Successful exposure requires acknowledgments for all selected notes and has
their durable-reservation events in the earlier log. Successful confirmation
requires a positive authenticator result, chain and transaction identity,
exact decoded events, and the selected note list to equal the configured
withdrawals. An unknown batch rejects preparation, signing, reservation,
exposure, and send. `#print axioms` reports only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` for these 16 theorems. The focused
`tests/EffectRefinement.lean` runs both one-note and two-note traces with
public synthetic data, including a deliberately missing second reservation
and a deliberately missing second withdrawal event.

## Assumptions and runtime coverage

The proofs do **not** establish that a `reserve` or `reserveNote` transition
corresponds to an actual durable, exclusive file write. The effect driver proves
ordering **assuming its `DurableAck` is truthful**; it cannot stop a broken
adapter from fabricating an acknowledgment. Runtime commands have protected
exclusive/CAS journals and injected fault tests for failed writes, concurrent
claims and ambiguous exposure. Those implementations are separate from these
pure drivers, and no theorem relates their complete execution traces. The
required filesystem operations are supplied by a trusted POSIX binding; see
[`STORAGE_BOUNDARY.md`](STORAGE_BOUNDARY.md).

The bridge takes receipt status, logs, expected pool/recipient/nullifier/fee,
and the current policy state from its caller. It checks byte-level consistency
without authenticating RPC provenance, finality, or the state's durable
reachability. The abstract effect driver additionally trusts its injected
receipt authenticator. Its synthetic test authenticator is not Ethereum
consensus verification. Runtime receipt parsers check exact transaction,
chain and event bindings against configured endpoint claims; those checks do
not authenticate chain truth.

The specification and abstract drivers cover one-note and batch withdrawal
policy transitions. They are not the runnable `WithdrawalSend`, relayer,
deposit or recovery command drivers. Relayer fee validation does reuse the
proved pure fee policy, but that reuse does not certify the complete command.
Cryptographic soundness, witness/circuit correspondence, deployed contracts,
network behavior, secret handling and filesystem durability remain separate
unproved properties or trusted boundaries. A successful Lean kernel check
therefore does not establish full CLI correctness.
