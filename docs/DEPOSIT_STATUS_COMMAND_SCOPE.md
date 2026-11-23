# Native deposit status reconciliation

[`Tornado/Cli/DepositStatusCommand.lean`](../Tornado/Cli/DepositStatusCommand.lean)
implements `deposit status --journal <path> [--rpc <url>]
[--bundler-url <url>]` for sequential and Simple7702 batch journals. It reads
the original protected journal, verifies the selected RPC chain, queries
receipts, and writes updated statuses back to the same journal. No transaction
is signed or sent. The CLI exposes this module through `deposit status`;
deposit submission uses separate send adapters.

Sequential deposits require the recorded transaction hash, account sender,
pool destination, successful receipt, and exact pool `Deposit` event for the
recorded commitment before they become `confirmed`. Approval and reset steps
require the recorded hash, sender, destination, and successful receipt.
Missing, malformed, or conflicting receipts become `unknown`; a matched
reverted sequential receipt becomes `reverted`.

For Simple7702 batches, a bundler receipt or filtered EntryPoint log may
suggest a transaction hash. A batch becomes `confirmed` only from the chain
receipt for that hash, addressed to the pinned EntryPoint, with the unique
reviewed `UserOperationEvent` and **every** selected pool `Deposit` event.
Missing or conflicting evidence remains `unknown`, and the command warns
against blind resubmission. A failure is reported only when an exact matching
UserOperation event proves failure; an unrelated outer reverted receipt does
not establish that result. The command accepts at most 12 reviewed deposits
per batch and rejects pool identities outside the pinned catalog.

[`ProtectedIO.replacePrivate`](../Tornado/Runtime/ProtectedIO.lean) is a small
native compare-and-replace boundary. It creates an exclusive owner-only
sidecar lock in the journal's trusted directory, checks the existing file's
inode, metadata, and exact original bytes, writes a new owner-only temporary
inode, syncs it, atomically renames it over the journal, and syncs the parent
directory before removing the lock. A stale expected value cannot overwrite
a newer journal. Pre-rename errors leave the original intact. A failure after
rename may mean the replacement happened but was not made durable; the error
text says to inspect the journal before retrying. A crash can leave the lock
sidecar behind. After confirming no process is updating the journal, inspect
the journal and chain state before manually removing that lock; the command
will fail closed while it exists.

The RPC and bundler are external trust boundaries. A receipt is not an
Ethereum consensus proof or finality guarantee, and a reorg can change a
previous status. Queries expose transaction or UserOperation hashes and
possibly commitments to the configured endpoints. The native transport
requires HTTPS for remote endpoints and permits explicit loopback HTTP for
local development. Run the offline reconciliation fixture with
`lake env lean --run tests/DepositStatusCommand.lean` and the native file
fault fixture with `lake build protected_replace_test` followed by
`.lake/build/bin/protected_replace_test <new-owner-only-directory>`.
