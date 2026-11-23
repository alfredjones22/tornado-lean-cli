# Native Lean pool-history reducer scope

`Tornado/Protocol/HistoryReducer.lean` is a pure selected-pool replay component.
It is based on the pinned `tornado-cli-new-era` commit
`daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7` and its
`@kohaku-eth/tornado-cash@0.1.0-alpha.38` state manager. The native history
orchestrator uses it for reports, preflight and experimental withdrawal
sessions; fetching and persistence are separate runtime components.

## Implemented

- A fresh state starts at `registeredBlock - 1`. Cached state is checked for
  the selected chain and pool, a valid cursor, contiguous deposit indices in
  leaf order, unique commitments and nullifiers, valid 32-byte identifiers,
  and event blocks inside the saved range.
- `applyBatch` refuses a gap after the saved cursor, a head behind the saved
  cursor, replay before a saved finalized cursor, a regressed finality claim,
  wrong-chain/pool events, malformed logs, out-of-order events, duplicate
  commitments or nullifiers, and missing/duplicate leaf indices. It prunes
  records from the replay start before adding replacement events. This models
  the SDK's rewind and `prunePoolFromBlock` transition, with stricter rejection
  of duplicate Map keys and malformed cached state.
- The supplied `onchainClaimBlock` must equal the replay coverage block.
  The resulting deposit count must equal the supplied same-block leaf count.
  A nonempty deposit tree is rebuilt with native Lean MiMC and must equal the
  supplied same-block root. Empty trees retain the supplied root, matching
  the SDK's empty-tree treatment. A partial Saga range therefore cannot be
  checked against a root from the later captured head.
- `applySaga` and `applyRpc` bind the pure reducer to the selected pool and
  already validated Saga or RPC event containers. The reducer re-decodes
  every event because those containers can also be constructed directly by a
  caller.
- A finalized cursor is never advanced just because the scan began there.
  If the supplied finalized head is before registration, the result keeps no
  finalized cursor. This is intentionally stricter than the alpha.38 SDK's
  `max(fromBlock, finalizedHead)` assignment, which could overstate finality
  when a provider supplies a stale finality head.

## Proofs and checks

Three Lean theorems import the actual reducer functions:

- `appendDeposit_success_next_index` proves a successful append has precisely
  the old array length as its leaf index and increases the length by one.
- `applyBatch_success_bound` proves that any returned result passed the
  executable chain/pool/cursor/count/root postcondition.
- `applyBatch_success_identity` extracts exact selected chain, pool,
  registration, cursor, deposit count, and root equalities from that check.

`#print axioms` reports only Lean's standard `propext` and `Quot.sound` for
these theorems. They do not prove the Merkle hash function correct, that the
RPC supplied true same-block claims, or that its event list was complete.
The six public roots in `fixtures/history-reducer-vectors.json` were generated
from the pinned SDK's `@kohaku-eth/mimc-tree@0.0.3` package. The focused Lean
test checks roots for one, two, and three leaves; reorg replacement of one
leaf and one withdrawal; empty-state finality; Saga/RPC adapters; wrong claim
block; and malformed or conflicting events. Reproduce with:

```sh
lake build Tornado.Protocol.HistoryReducer
lake env lean --run tests/HistoryReducer.lean
node scripts/generate-history-reducer-vectors.mjs --check
```

## Trust and integration limits

The leaf count and root remain **caller-supplied RPC claims**. The equality of
`onchainClaimBlock` and the replay coverage block is an input label check, not
proof that the RPC actually queried that block. A production caller must bind
both calls to one configured chain/endpoint/block and authenticate the selected
pool and its deployed code. Even a matching deposit count/root cannot detect
an omitted `Withdrawal` event: withdrawals do not change the deposit tree.
Before spending, query the selected note's nullifier through the pool's
`isSpent` method at the captured head, reconcile it with withdrawal history,
and fail closed on disagreement.

The reducer caps deposit leaves at 2²⁰, cached withdrawals and one replay at
one million records each, then rebuilds a full 20-level tree and accepts
in-memory event arrays. These caps bound the algorithm but still permit high
peak memory; there is no streaming index/frontier in this reducer. It does not
fetch history, verify signed Saga indexes,
recover from a tree mismatch by rescanning chain-only logs, persist a public
snapshot, authenticate chain finality, or bind a note's private identity to a
Merkle path. A lie from the sole RPC or an omitted event can survive all pure
checks. Experimental withdrawal sessions reach the reducer through
`HistorySync`, then independently check the selected note's history and spent
state before preparing public proof inputs.
