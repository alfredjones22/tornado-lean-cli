# Native batch 4337 withdrawal status scope

[`Tornado/Cli/BatchWithdrawalStatus.lean`](../Tornado/Cli/BatchWithdrawalStatus.lean)
provides reconciliation and protected persistence for `batch-4337`
status files. It accepts `--status-file <path>`, optional `--rpc <HTTPS URL>` and
`--bundler-url <HTTPS URL>`, and `--help`. The selected file must be listed in
the record's same-directory, opaque per-note `statusFiles` paths. The command
checks the configured chain ID and pinned EntryPoint, paymaster, and Tornado
pool addresses before using the recorded candidate hashes.

For every signed candidate, a recorded transaction hash, a bundler receipt
hint, or a unique matching EntryPoint log locates a transaction. Only the
**exact chain receipt** can establish an outcome. The receipt must match the
requested transaction hash and recorded block range, be addressed to the
pinned EntryPoint, contain exactly one matching `UserOperationEvent` for that
candidate, and, for `confirmed`, contain an exact `Withdrawal` event for
**every** selected note. Each event is checked against its pool, nullifier,
recipient, relayer, and fee. The generic receipt parser also checks all log
transaction and block metadata and rejects removed logs. A bundler response
alone cannot confirm or fail a candidate. Missing, malformed, or ambiguous
evidence remains `unknown`.

The aggregate is `confirmed` when exactly one candidate confirms and no
candidate fails; `failed` only when every candidate has an exact failed
EntryPoint event; otherwise it is `unknown`. A `confirmed` result exits 0 only
after the complete journal update; all other results exit 2. A failed EntryPoint operation may still have spent
the sponsoring note, so its output instructs recovery of the smart account
and checking every selected note before retrying.

Before writing, the command reads and validates **every listed mirror**.
They must have the same full signed-candidate set, exact per-candidate event
tuples, chain, account, nonce, endpoints, note ordering, path list, and other
immutable reservation fields. Only mutable observations may differ. Known
candidate transaction hints are merged without replacing or dropping one.
Conflicting hints, missing mirrors, and inconsistent reservations fail before
the first write. An aggregate transaction hint must remain retained by a
candidate.

The first path in `statusFiles` is authoritative for the native update's
completion marker. A protected compare-and-replace first writes its new
observation with `nativeBatchStatusSync.state = "in-progress"`. Every other
mirror is then replaced against its exact pre-read bytes, retaining all
candidates and reservations. Only after every mirror write is acknowledged
does the command mark the first record `complete`. The marker is additional
observation metadata; it does not change the reserved candidate identity.

A crash or failed CAS can leave partially refreshed observations. The
in-progress marker and reservations remain present, the command reports
incomplete synchronization and exits 2, and a later native status command can
reconcile again from any listed mirror. An error after a rename can mean a
write completed, so acknowledged-write counts are not exact disk-state
counts. A stale or concurrent writer cannot overwrite changed bytes. This is
recoverable observation mirroring, not atomic multi-file replacement or a
lock honored by every external client.

No path, candidate or reservation is deleted, and failed or partially saved
observations never authorize a retry. A `complete` marker records acknowledged
writes for that update; subsequent modifications or reorgs need another check.
Send guards must continue refusing new signatures while these reservation
files exist.

The selected HTTPS RPC is assumed to report canonical chain data honestly;
this module does not verify Ethereum consensus or finality. Reorgs can change
a previously observed receipt. `eth_getLogs` scans from the stored block to
`latest` using the candidate's public UserOperation hash and can exceed a
provider's range limit, yielding `unknown`. These lookups expose the hash to
the selected RPC or bundler. No note secret, proof, signature, or raw
UserOperation is sent by this module. Explicit loopback HTTP RPCs are supported
for local development; remote endpoints require HTTPS. The offline fixture test also covers missing/different
mirrors, known and conflicting transaction hints, ambiguous partial CAS,
authoritative commit failure, and recovery through either mirror:

```sh
lake build Tornado.Cli.BatchWithdrawalStatus
lake env lean --run tests/BatchWithdrawalStatus.lean
```
