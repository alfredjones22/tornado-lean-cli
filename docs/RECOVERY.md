# Recovery and interrupted operations

Keep the original note backup, journal, status files and reservation directory.
They identify what was signed or exposed. An error, timeout, failed simulation
or missing receipt does not establish that nothing happened. Reconcile the
original candidate before attempting another transaction.

## Existing files and locks

Exclusive creation deliberately rejects an occupied output, sender lock or
per-note claim. An existing file is not necessarily stale. Deleting it can
remove the protection against signing or funding the same operation twice.

Sender locks coordinate deposit, batch-withdrawal and recovery commands using
the same protected key directory. Interactive deposits and recovery anchor
reservations beside their journal; interactive batch withdrawals use the home
directory. Per-note withdrawal paths also coordinate sponsored and Classic
relayer routes within one status directory. Copying a backup or key to another
directory does not provide global coordination.

A protected journal replacement uses an exclusive sidecar lock and a
byte-for-byte comparison with the previously read file. A crash can leave a
sidecar behind. A failure after rename can mean the replacement already
happened. Before manually removing a stale sidecar, establish that no process
is updating the journal, inspect the file and reconcile the recorded chain
outcomes. Do not clear sender locks or note claims merely to bypass an error.

## Resume a sequential ETH deposit

Only sequential ETH deposit journals support `deposit send --resume`. Use the
same ordered notes, sender, original journal and reservation location:

```sh
lake exe tornado deposit send --notes-file ./notes.txt --key-file ./key.txt --chain 11155111 --journal ./journal.json --resume --dry-run
lake exe tornado deposit send --notes-file ./notes.txt --key-file ./key.txt --chain 11155111 --journal ./journal.json --resume --broadcast
```

Use the intended chain; the example selects Sepolia. Omit `--key-file` for
hidden terminal entry, or add `--non-interactive` with an explicit protected key
file to authorize unattended broadcasting. The dry-run changes no journal or
reservation.

Resume checks the complete original plan and sender, all recorded transaction
hashes, indexed calls, receipts, block identity, Deposit events and commitment
registration. It requires a recorded prefix followed by a never-exposed planned
suffix. Confirmed deposits are skipped; only the remaining suffix can be signed.
Each new candidate is reserved in the original journal before exposure.

Pending, unknown, reverted, missing or contradictory evidence, unexpected
nonce activity, a changed plan or a conflicting claim stops continuation.
Existing recorded claims must still match the original journal; missing claims
for recorded steps cannot be recreated. A missing claim can be admitted for a
never-exposed planned step. Completion releases only the matching sender lock.

This path rejects legacy token-approval and ERC-4337 batch journals. It does not
guess how to replace a reverted transaction or resolve an ambiguous send. A
new invoice is not a substitute for reconciling the original plan.

## Inspect deposit status

```sh
lake exe tornado deposit status --journal ./journal.json
lake exe tornado deposit inspect-status --journal ./journal.json
```

Both commands send no transaction and require no signing key. `deposit status`
updates the protected sequential or Simple7702 journal through compare-and-
replace. `deposit inspect-status` only reads sequential journals and prints its
observations; it rejects batch journals and does not save statuses.

Sequential deposits require the exact recorded transaction, sender, pool,
successful receipt and commitment's Deposit event. Approval/reset steps require
the exact successful receipt; that alone does not prove a token allowance's
post-transaction value. A matched reverted receipt is `reverted`; missing,
malformed or conflicting evidence is `unknown`.

A Simple7702 batch needs a receipt addressed to the pinned EntryPoint, exactly
the matching UserOperation event and every expected Deposit event. A bundler
receipt or EntryPoint log may locate a transaction, but is only a hint. An
unrelated outer transaction failure does not prove that the reviewed operation
failed. Updating status does not itself authorize a resend.

## Reconcile withdrawals

```sh
lake exe tornado withdraw status --status-file ./withdrawal-status.json
```

Use an original protected status file. Supported formats are one-note 4337,
Classic relayer and batch 4337. The command may update observations through
protected compare-and-replace; it never signs or submits a replacement. RPC and
bundler options override the saved endpoints only where supported.

For sponsored withdrawals, confirmation requires the exact receipt and matching
EntryPoint event plus every selected pool Withdrawal event. Pool, nullifier,
recipient, relayer and fee must match the reserved candidate. A bundler
acknowledgment, transaction hint or timeout is not confirmation.

For Classic relayers, only the exact pool Withdrawal event and successful
matching transaction receipt confirm. The status command does not query relayer
job progress. An absent event is not proof that a note is unspent or safe to
resubmit. Its fallback scan is capped at 1,024 windows of 1,000 blocks and
100,000 logs; unavailable or incomplete evidence remains `unknown`.

Nonconfirmed withdrawal status reports exit code 2. This signals uncertainty or
failure, not permission to sign again. A saved signed candidate or occupied
claim continues to block replacement, including a switch to a different route.

### Batch status mirrors

Batch status first validates every listed mirror: candidates, immutable
reservation fields, note ordering and paths must agree. Only observations may
differ. Known transaction hints are retained, and conflicts stop writes.

The first `statusFiles` path is authoritative. Its update is marked
`nativeBatchStatusSync.state = "in-progress"`, the remaining mirrors are
compared and replaced, and only then is the first marker set to `complete`.
Secondary mirrors can retain an in-progress marker after successful completion;
the authoritative first record determines that update's completion.

A partial write or crash reports incomplete synchronization and exit code 2.
Re-running status from any listed mirror can reconcile again. No candidate,
path or reservation is deleted. `complete` means that the observation update was
acknowledged; it does not establish transaction success or finality.

### Failed execution and stranded funds

The sponsoring note is withdrawn during paymaster validation. Later execution
failure can leave that note spent and funds in the recoverable smart account.
It does not establish an atomic rollback of the whole batch. Reconcile the
original operation and every selected note before taking further action.

## Recover a smart account

```sh
lake exe tornado smart-account show --owner 0xYourOwner --chain 1
lake exe tornado smart-account recover --owner 0xYourOwner --chain 1 --dry-run
lake exe tornado smart-account recover --owner-key-file ./key.txt --chain 1 --broadcast --journal ./recovery.json
lake exe tornado smart-account status --journal ./recovery.json
```

The public-owner dry-run needs no key. Broadcasting uses a protected owner key
file or hidden terminal entry, defaults to typed `RECOVER`, and requires a new
journal. `--non-interactive` requires an explicit protected owner-key file.
The receiver defaults to the owner; `--receiver` can select another address.
Recovery gas is paid by the owner.

The review checks the predicted pinned account, factory/implementation identity,
owner, EntryPoint, nonce and supported balances at one captured block. It builds
ordered supported ETH/ERC-20 sweeps and optional withdrawal of that smart
account's EntryPoint deposit. Unsupported tokens or NFTs need separate
owner-authorized actions. Empty/undeployed accounts, self-recipients and
mismatched identities are rejected.

Approval is followed by fresh identity, balance and exact-call checks. The
candidate must be the reviewed zero-value type-2 owner transaction to the
account. Its hash is journaled before broadcast. Unknown signing/send outcomes
retain the shared sender lock. Confirmation requires the exact transaction,
calldata and successful receipt with consistent inclusion metadata.

`smart-account status` updates the original journal without a private key or
transaction send. Missing or inconsistent evidence is `unknown`, an exact
transaction without receipt is `submitted`, and an exact revert is `failed`.
It exits 2 unless confirmed. There is no automatic replacement or resend.

Unused gas credit from a self-funded delegated deposit belongs to the **sender
EOA's** EntryPoint balance. It is separate from this derived smart account and
is not swept by smart-account recovery. EntryPoint reuses it for future
self-funded UserOperations. The EOA owner can withdraw it with an ordinary
zero-value transaction to the pinned EntryPoint's `withdrawTo(owner, amount)`
method, paying that transaction's gas from the EOA. Deposits do not
automatically sweep this credit.

## What is proved, and what is assumed

The runtime uses finite journal and admission programs in
[`WithdrawalJournalProgram.lean`](../Tornado/Runtime/WithdrawalJournalProgram.lean)
and [`ReservationAdmission.lean`](../Tornado/Runtime/ReservationAdmission.lean).
Successful reservations retain the exact acknowledged create/CAS sequence and
reviewed record. Under an explicit filesystem/crash model,
`reserved_complete_physical` establishes the selected paths' exact bytes and
`reserved_then_crash_blocks_readmission` establishes occupied-path readmission
blocking after a modeled interruption. Only ENOENT means absence; unreadable,
partial, malformed and symlink entries are occupied or errors.

Admission is an observation, not a lock. Concurrent starts can both observe
absence and sign; only the winning complete exclusive reservation may proceed
to executable exposure. Per-attempt proofs do not prove global uniqueness of
signing. Batch repair certificates preserve immutable candidates and unknown
extension fields through staged writes. Shared single-file callbacks in other
senders do not constitute complete command refinement.

The separate `AttemptJournal`/`NoteClaims` examples have replay, exclusive-create
and process-race tests. They are not substitutes for a theorem about every live
sender. Native crash-cut tests exercise partial writes, lost replies, stale
locks and compare-and-replace; they do not prove real disk durability.

Send adapters proceed after one validated receipt inclusion, without a
twelve-block wait. Status is observed inclusion, not Ethereum finality. An RPC
can fabricate consistent evidence, and a reorg can reverse an observation.
Copied directories, manual deletion, hostile same-user modification, corrupt
storage and violated OS/device guarantees are outside the crash model. See
[Proof coverage](PROOFS.md), [Security specification](SECURITY_SPEC.md) and
[Trust boundaries](TRUST_BOUNDARIES.md).
