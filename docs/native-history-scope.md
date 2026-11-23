# Native Lean Saga history boundary

Pinned source: `tornado-cli-new-era` main commit
`daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7`, especially
`src/services/saga-history.ts`, `src/services/history.ts`, and
`src/runtime/protocol.ts`. This is a bounded pure component used by the native
history orchestrator and withdrawal sessions; it is not a standalone provider
or Ethereum consensus authenticator.

## What the component checks

- `planIndex(selection, indexBytes)` parses an index of at most 2 MiB, selects
  exactly one `tornado-cash` stream for the requested chain and pool, computes
  the alpha.38 legacy rewind, and rejects segment gaps, overlaps, unsafe
  filenames, unsupported metadata, and a cursor beyond the captured head.
  A fresh snapshot cursor one block before registration is accepted and the
  replay start is clamped to registration.
- `validateChunks(plan, bytesInManifestOrder)` checks the exact chunk count,
  bounded gzip integrity, SHA-256 of **decompressed** bytes, valid UTF-8 and
  JSONL, event range and strict ordering, tracked addresses, topic consistency,
  strict Tornado `Deposit`/`Withdrawal` ABI, and optional transaction hashes.
  It returns no coverage until **every** selected chunk passes.
- `admitRange(history, from, to)` refuses a range outside validated inclusive
  coverage. Lean proves that every accepted request lies within the stored
  replay start and coverage.
- `validateCoverage` is the pure segment-chain gate used by `planIndex`.
  Lean proves that any accepted chain starts at or before the replay point,
  reaches past it, has exact adjacency across every later segment, and ends
  strictly after the replay point.
- `assertPoolFreshness(selection, syncedPool)` checks exact chain and pool
  identity and that the post-sync cursor reaches the captured head. Lean proves
  those equalities and the head bound when the check succeeds. A partial Saga
  stream requires RPC to fill the tail before this check can pass.
- Lean proves the computed rewind never precedes the pool registration block.
- `RpcHistory.requestParams` constructs an exact-pool `eth_getLogs` filter for
  at most 1,000 blocks within registration and the captured head. Lean proves
  that any accepted filter obeys those bounds.
- `RpcHistory.parseRange` checks the JSON-RPC envelope and request IDs,
  selected chain ID, 1 MiB response bound, requested pool and block range,
  block/transaction hashes, non-removed logs, strict order, and Tornado event
  ABI. Empty results are accepted as provider claims; they do not establish
  that the provider returned every event.

## Bounds and compatibility

The pinned TypeScript client permits 64 MiB compressed and 256 MiB decompressed
Saga chunks. The current native Lean gzip decoder has a 32 MiB hard limit for
both input and output. This component **fails closed** above 32 MiB. It also limits a chunk
to one million event records. The selected range is capped at 64 chunks,
256 MiB of aggregate supplied chunk bytes, and one million selected events.
The API accepts an in-memory array of all chunks, so live callers enforce
those budgets during fetching. There is no streaming validator; a late
validation error can follow substantial allocation and computation. HTTP
`Content-Encoding` may already decompress a
`.gz` payload, so it accepts either bounded gzip or bounded raw bytes, matching
the TypeScript behavior. It applies stricter canonical quantity syntax than
the pinned TypeScript parser, which can reject some otherwise usable streams.

## Integration API and obligations

1. Obtain an authenticated selected-chain RPC head and a validated local public
   snapshot. Check the snapshot's chain, pool address, asset, denomination and
   registration metadata against the selected catalog. Pass its exact pool
   address, registration block, last-synced cursor, and finalized cursor into
   `Selection`.
2. Use the bounded HTTPS GET binding for `index.json` and selected chunks.
   The GET boundary checks TLS, URLs, redirects, response sizes and timeouts;
   it does not authenticate Saga data. Use the
   `https://saga.0000000000.org` base for mainnet and its `/sepolia` path for
   Sepolia, unless the CLI configuration explicitly chooses another source.
   The `0000000000.org` proxy is required for browser CORS in the UI; the CLI
   may technically use direct HTTPS, but parity with the pinned CLI default
   uses this proxy.
3. Call `planIndex`, fetch exactly `plan.segments` in that order with per-chunk
   size/time limits and an aggregate fetch deadline, and fetch the mutable
   `hotHead` with no cache, then
   `validateChunks`. Convert its returned decoded events into the native sync
   state. Never expose `plan.coverage` as validated before
   `validateChunks` succeeds.
4. On any Saga failure, retain the protected local snapshot and use bounded
   `eth_getLogs` RPC fallback from the last trusted cursor. Include the Saga
   rewind overlap. `RpcHistory.requestParams` and `RpcHistory.parseRange` cover
   the pure request/response boundary. These modules do **not**
   implement the RPC fetch loop, state reducer, or disk persistence. Keep the
   chain ID request and log request on the same configured endpoint, split a
   rejected large range into smaller slices, and stop on any failed slice.
5. After native sync/import, call `assertPoolFreshness` for every selected pool,
   then verify each requested note resolves to the expected chain/pool. Do not
   prepare a withdrawal from incomplete or wrong-pool history.

## Trust limits

The SHA-256 checksum binds each chunk to the fetched index. The index is not
cryptographically signed. TLS and endpoint selection are therefore part of the
trust boundary. Neither this module nor an `eth_getLogs` response proves that
the endpoint returned *all* chain events: a lying provider can omit logs while
returning a syntactically valid response. The captured head, pool catalog,
snapshot metadata, reorg/finality handling, native sync reducer, and protected
filesystem writes remain outside these proofs. The formal claims concern the
Lean functions on their supplied bytes and parameters, not Ethereum consensus.
The SHA-256 and gzip implementations are native Lean and have vectors and
integrity checks, but this component does not include a full standards-level
proof that those implementations match every SHA-256/DEFLATE input.

## Files and validation

- `Tornado/Protocol/SagaHistory.lean`
- `Tornado/Protocol/SagaHistoryTests.lean`
- `Tornado/Protocol/RpcHistory.lean`
- `Tornado/Protocol/RpcHistoryTests.lean`
- `fixtures/saga-history/` (35 deterministic synthetic files)

The tests use fixture files directly. Their path defaults to
`fixtures/saga-history/` and can be overridden with
`TORNADO_SAGA_FIXTURES`. These deterministic synthetic fixtures are test data,
not captured canonical Ethereum history.

Focused validation from the Lean repository root:

```sh
lake build Tornado.Protocol.SagaHistory Tornado.Protocol.RpcHistory
lake env lean --run Tornado/Protocol/SagaHistoryTests.lean
lake env lean --run Tornado/Protocol/RpcHistoryTests.lean
```

Observed: `Saga history: 28 offline fixture assertions passed` and
`RPC history: 14 offline fixture assertions passed`.
