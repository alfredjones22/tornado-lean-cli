# Native Classic relayer withdrawal status

[`Tornado/Cli/RelayerWithdrawalStatus.lean`](../Tornado/Cli/RelayerWithdrawalStatus.lean)
reconciles a protected TypeScript Classic-relayer status record using the
selected Ethereum RPC. It validates the chain and pinned original Classic
pool, scans the recorded `fromBlock` through the current head in bounded
`eth_getLogs` windows, and checks an exact on-chain pool `Withdrawal` event
against the recorded nullifier, recipient, relayer reward address, and fee.
The event's transaction hash must lead to a successful receipt addressed to
that pool, with the same block identity and an exact matching event. A
recorded transaction hash can also be checked directly when no scan range is
available. Only this evidence yields `confirmed` and exit code 0.

This implementation does **not query the relayer job endpoint**. A relayer's
job ID is printed for reference but is not treated as proof. Pending, failed,
no-job, no-range, RPC outage, malformed data, incomplete scan, multiple
matching events, and conflicting withdrawal details stay `unknown` (exit
code 2). This is conservative partial parity with the pinned TypeScript
command, which can also report relayer `pending` or `failed` from job claims.
The scan is capped at 1,024 windows of 1,000 blocks and 100,000 returned
logs; older or unusually large ranges need manual or further tooling.

The command accepts `--status-file <path>`, optional `--rpc <HTTPS URL>`, and
`--help`; it tolerates the parent `withdraw status` command's
`--bundler-url <url>` but does not use it. It updates the original protected
status file through `ProtectedIO.replacePrivate(path, originalBytes,
updatedBytes)`, which guards against concurrent changes using a same-directory
exclusive lock and atomic compare-and-replace. A stale lock after a crash
requires manual inspection before removal, as described in
[`DEPOSIT_STATUS_COMMAND_SCOPE.md`](DEPOSIT_STATUS_COMMAND_SCOPE.md).

The `eth_getLogs` filter contains the pool address and public Withdrawal
event topic, **not the unspent nullifier hash**; comparison happens locally.
RPC responses still depend on provider honesty and canonical chain history.
A missing event is not proof that the note is unspent or safe to resubmit, and
a reorg can invalidate a prior confirmation. RPC endpoints may use HTTPS or
explicit loopback HTTP; relayer service endpoints still require HTTPS.
Run the offline fixture with
`lake env lean --run tests/RelayerWithdrawalStatus.lean`.
