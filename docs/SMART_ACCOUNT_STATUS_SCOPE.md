# Smart-account recovery status

`smart-account status --journal <path> [--rpc <url>]` reads a protected
recovery journal, checks the selected RPC's chain ID,
and queries the recorded transaction and receipt. It reports `confirmed` only
when the indexed transaction has the exact recorded hash, owner sender,
smart-account destination, zero value, type-2 envelope, calldata hash, and selected chain; the receipt must
also have the same hash, sender and destination, matching transaction inclusion
block hash/number/index, and a successful status. A
reverted exact receipt reports `failed`. Missing, malformed or conflicting
evidence stays `unknown`, while a matched transaction without a receipt stays
`submitted`. The command exits with code 2 unless confirmed.

The native command updates the journal through protected byte-for-byte
compare-and-replace. A concurrent edit or stale snapshot prevents replacement.
Candidate identity and transaction/calldata hashes are preserved. The injected
recovery tests also cover CAS failure and unchanged prior evidence.
Neither command can prove that the configured RPC speaks for Ethereum
consensus or that a receipt is final. A same-user journal edit, malicious RPC,
or later reorg remains outside the guarantee.
The native transport accepts HTTPS or explicit loopback HTTP for local
development; remote plaintext RPCs are rejected.

[`SmartAccountStatus.lean`](../Tornado/Cli/SmartAccountStatus.lean) contains
the protected journal parser, transaction and receipt gates, and an injectable
RPC read adapter. Two Lean theorems prove that a `confirmed` result passed the
recorded transaction and inclusion checks. The offline test covers journal rejection, exact
success/revert/pending/unknown outcomes, altered sender/calldata/chain,
malformed receipts, stale inclusion metadata, and a wrong RPC chain. It does
not require a live RPC.

Run `lake env lean --run tests/SmartAccountStatus.lean`. This command reads no
private key, signs nothing, and sends no transaction.
