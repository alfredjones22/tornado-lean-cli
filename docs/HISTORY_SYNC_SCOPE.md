# Read-only native pool-history sync boundary

`Tornado/Runtime/HistorySync.lean` connects the existing native Saga validator,
RPC log validator, and selected-pool reducer to the reviewed HTTPS GET/POST
binding. It accepts one caller-supplied `HistoryReducer.State` and returns a new
state only after the selected pool's cursor reaches a captured RPC head. It
serves history, compliance, withdrawal preflight and live public withdrawal
sessions, with pinned snapshot/cache support in separate adapters. Callers
establish catalog pool identity, registration block and saved state; the sync
does not authenticate Ethereum consensus.

## What the implementation checks

1. The configured RPC returns the expected chain ID. Its block number is
   captured once as the synchronization target. The same RPC transport is used
   for all later chain checks, logs, and exact-block `nextIndex()` and
   `getLastRoot()` calls.
2. The default Saga base is `https://saga.0000000000.org` on mainnet and
   `/sepolia` on Sepolia. The index and selected chunks pass the pure Saga
   metadata, digest, event, pool, ordering, and coverage validators before any
   Saga state is accepted. A failed Saga attempt falls back to RPC from the
   original state; no partial Saga cursor escapes.
3. A partial Saga range is followed by an RPC tail. On Saga failure, RPC starts
   at the reducer's rewind point. `eth_getLogs` requests are exact-pool,
   inclusive ranges of at most 1,000 blocks. Request failures and explicit
   range-limit errors are bisected at most ten levels; malformed returned logs
   are rejected. All slices must be contiguous through the captured head
   before the reducer sees any of them.
4. The reducer replays events and checks deposit count and computed nonempty
   MiMC root against `nextIndex()` and `getLastRoot()` at the Saga coverage
   block or captured head. The success gate then checks selected chain, pool,
   and cursor. Lean proves that successful admission has these last three
   properties. A separate theorem certifies the aggregate-byte predicate.

Limits are a five-minute aggregate deadline, 4,096 RPC requests, 256 MiB of
aggregate transferred response bytes and 256 MiB of aggregate decoded Saga
bytes, one MiB per RPC response, two MiB per Saga index, 32 MiB per
compressed/decoded Saga chunk, 64 selected segments, one million
combined events, and two million RPC-scanned blocks. The underlying HTTPS
binding has a 10-second connection timeout, 30-second POST timeout, and
60-second GET timeout. The aggregate deadline is checked between requests, so
one in-flight call can exceed it by its own timeout.

`tests/HistorySync.lean` uses a deterministic injected transport. It covers
complete Saga, partial Saga with an RPC tail, invalid index and chunk fallback,
bounded RPC splitting and reassembly, wrong chain/pool/root/count, removed
logs, a malformed second slice, deadline failure, exact aggregate-byte
boundary, and a deliberately omitted withdrawal log. Run:

```sh
lake build Tornado.Runtime.HistorySync
lake env lean --run tests/HistorySync.lean
```

## What a successful result does not establish

- HTTPS authenticates the configured endpoints, not the truth or completeness
  of their responses. A provider can omit a withdrawal event while returning
  the correct deposit root and count; the omission test intentionally
  demonstrates that the sync can accept such a response. Even the same RPC
  could give mutually consistent but false logs and contract-call answers.
- The Saga index is not signed or independently pinned. SHA-256 checks that
  chunks match the fetched index, not that the index describes canonical chain
  history. The same-block RPC claim adds one consistency check, not consensus.
- A captured `eth_blockNumber` is not an authenticated finalized head. This
  module never promotes a new finalized cursor; it carries forward the
  caller's prior finalized claim. A false prior finality claim may prevent
  necessary rewind after a reorganization.
- The module does not verify `isSpent` for every withdrawal, prove empty-range
  completeness or authenticate deployed pool code. Catalog identity and
  selected-note checks are performed by its callers. It supplies
  consistency-checked provider claims, not a
  standalone justification for a fund-moving transaction or proof of chain truth.
- A failed sync returns an exception and no new `State`. The core `syncWith`
  does not persist state; `syncSelectedPoolWithAssets` additionally imports
  pinned snapshots and persists a successful public result through the
  protected chunk/cache adapter. Cache integrity, CAS and reorg behavior have
  focused tests, not filesystem durability proofs; see
  [snapshot scope](HISTORY_SNAPSHOT_SCOPE.md).

The two Lean theorems have no `sorryAx`; their reported axioms are only
Lean's ordinary `propext`, `Classical.choice`, and `Quot.sound` where used.
They prove control-flow admission and a numeric bound, not the behavior of
libcurl, remote providers, operating-system clocks, or chain consensus.
