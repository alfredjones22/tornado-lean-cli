# Read-only sequential deposit inspection

`Tornado/Cli/DepositStatus.lean` implements `inspectCommand`, a **read-only**
inspector for a version-1 sequential `deposit` journal. Main exposes it as
`deposit inspect-status`, a distinct command because
its behavior differs materially from the mutable `deposit status` command.

The native inspector accepts `--journal <path>` and optional `--rpc <https-url>`.
It reads the file through the protected POSIX binding, validates the version,
chain, sender, step kinds and statuses, exact transaction hashes, and pinned
pool/commitment identity. It rejects 7702 batch journals before any network
request. For a sequential journal it checks `eth_chainId`, queries one receipt
per recorded hash through the HTTPS JSON-RPC binding, and parses receipts with
`RpcReceipt.parseReceipt`. It reports `confirmed` only when the transaction
hash, sender, destination, receipt success, and a strictly decoded Deposit
event match the pinned pool and recorded commitment. Missing or malformed
receipt evidence is `unknown`; an exact reverted receipt is `reverted`.
Approval and reset steps confirm on a successful exact receipt; this does not
prove the token allowance's post-transaction value.

Output includes per-step rows and `Read-only inspection; journal statuses
were not updated.` The inspector does not mutate files, send
transactions, or sign anything. The separate `DepositStatusCommand.lean`
implements mutable sequential/7702 reconciliation through protected
compare-and-replace; see [command scope](DEPOSIT_STATUS_COMMAND_SCOPE.md).

`scripts/deposit-status-source-check.mjs` regenerates the public synthetic
fixture from an independently pinned journal constructor. The generator
retains its exact source identity.
`tests/DepositStatus.lean` checks its parsing, exact receipt classification,
wrong hash/sender/destination, missing Deposit event, reverted receipt,
malformed journal rejection, and output warning. No live RPC was used.

TLS authenticates the configured endpoint, not Ethereum consensus. Neither
this module nor the existing receipt parser proves canonical-chain membership,
finality, or that the local journal came from an actual signed transaction.
An endpoint can claim a false receipt, and a reorganization can change a
previous result. These remain critical boundaries before funds depend on the
reported status.
