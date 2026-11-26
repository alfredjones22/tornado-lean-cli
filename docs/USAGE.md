# Using the Tornado CLI

The native build needs `pkg-config`, OpenSSL libcrypto 3.2+ and libsodium
1.0.18+. See [Verification prerequisites](VERIFICATION.md) for installation and
custom library prefixes. Build both executables from the repository root:

```sh
lake build tornado tornado_prover_worker
lake exe tornado --help
```

Examples below use Ethereum mainnet. Commands accepting `--chain` default to
`1`; use `--chain 11155111` for Sepolia notes. Status commands obtain the network
from their journal. New preparations use `--rpc`, then `TORNADO_RPC_URL`, then
the network default; status reconciliation may reuse its saved endpoint.
Remote endpoints require HTTPS; explicit loopback HTTP is allowed for local
development. Consult each command's `--help` for its accepted options.

The CLI performs selected checks and has selected formal proofs. It does not
guarantee bug-free code, loss-free operation or anonymity. Read the
[security specification](SECURITY_SPEC.md), [proof coverage](PROOFS.md) and
[trust boundaries](TRUST_BOUNDARIES.md) before using funds.

## Backups, keys and approval

Keep note backups private and recoverable: possessing a note allows spending
it. Newly created backups use exclusive creation with mode `0600`; existing
files are never overwritten. Protected-file reads reject unsafe ownership,
permissions, symlinks, multiple hard links and access-granting macOS ACLs.
Paths may be absolute or relative, but `..` components are rejected.

For deposits use `--key-file`; for batch withdrawals or recovery use
`--owner-key-file`. The file can contain a raw, `0x`-prefixed 32-byte private
key or an Ethereum Web3 Secret Storage v3 encrypted account keystore. Both
formats require `chmod 600` and no access-granting ACLs. Omitting the file
option opens a hidden raw-key terminal prompt. Keys are handled inside the native signer boundary; note
secrets and the isolated prover retain the limitations in
[trust boundaries](TRUST_BOUNDARIES.md).

### Encrypted account keystores

Key-file commands automatically recognize standard v3 JSON keystores used by
Foundry/cast, geth and ethers. Supported encryption is AES-128-CTR with either
scrypt or PBKDF2-HMAC-SHA256 and the Ethereum Keccak-256 MAC. The loader accepts
`crypto` or `Crypto`, verifies the MAC before decryption, and checks any stored
address against the decrypted key. Legacy/presale and validator keystores are
different formats and are not accepted.

An encrypted file prompts once for its password with terminal echo disabled.
Use `--pwd-file <private-password-file>` or `--pwd-file=<path>` to read it from
a protected file instead. The option requires an encrypted key file and
applies to deposits, invoice payment, deposit resume, batch withdrawals and
smart-account recovery, including their review/dry-run modes.

With `--non-interactive`, an encrypted file requires `--pwd-file`;
otherwise the command errors before network preparation, reservations or
signing. A raw key file needs no password. One-note withdrawals derive their
own signer from the note and do not accept account-key password options.

```sh
lake exe tornado deposit send --notes-file ./notes.txt --key-file ./keystore.json --chain 1 --dry-run
lake exe tornado deposit send --notes-file ./notes.txt --key-file ./keystore.json --pwd-file ./password.txt --chain 1 --non-interactive --dry-run
lake exe tornado withdraw batch --notes-file ./notes.txt --owner-key-file ./keystore.json --pwd-file ./password.txt --chain 1 --non-interactive --dry-run
```

Passwords are read only through hidden entry or a protected file, not command
arguments. Password files use the same protected-file policy and must be mode
`0600`. Their contents are exact UTF-8 bytes, preserving spaces; one final LF
or CRLF is removed. No Unicode normalization is performed: supply the same
password bytes used to create the keystore. For ethers-created string-password
keystores, this can mean supplying NFKC-normalized bytes.
An empty supplied password is distinct from no password. Password size and
KDF work are bounded; an excessive keystore is rejected without weakening its
parameters. The JSON limit is 64 KiB, password limit 1,024 UTF-8 bytes, and
derived-key size 32–1,024 bytes. PBKDF2 admits at most 10 million iterations;
scrypt admits at most 512 MiB estimated workspace and `N*r*p <= 2^25`, with
power-of-two `N <= 2^20` and positive `r,p <= 1,024`. Canonical ASCII JSON field
names are required. No plaintext key file is written. The command retains the original
keystore path for reservations and rechecks the protected source before each
use of its native unlocked session.

### Review and broadcasting

Run `--dry-run` first, then issue a separate command with `--broadcast`.
Sending defaults to typed `SEND`, `WITHDRAW` or `RECOVER` approval; new or
replaced deposit delegations also require `DELEGATE`. Explicit
`--non-interactive` skips those prompts while still printing the review and
running validation, fee bounds, revalidation, journals and reservation checks.
It does not enable broadcasting by itself. Unattended deposits require
`--key-file`; batch withdrawals and live recovery require `--owner-key-file`.
One-note withdrawals use the protected note backup without an account key.
Live commands do not accept `--yes` as authorization.

## Select pools and create notes

```sh
lake exe tornado pools --chain 1 --asset ETH
lake exe tornado deposit plan --chain 1 --asset ETH --amount 1.4
lake exe tornado notes create --chain 1 --asset ETH --denom 0.01 --count 2 --out ./notes.txt
lake exe tornado notes inspect --file ./notes.txt
lake exe tornado notes invoice --file ./notes.txt
```

`notes create` creates one denomination, repeated `--count` times. To create
one backup spanning an exact mixed-denomination plan:

```sh
lake exe tornado notes create-plan --chain 1 --asset ETH --amount 1.4 --out ./planned-notes.txt
```

`--exclude <denominations...>` restricts the plan. `--plan <n>` selects a
1-based alternative shown by `deposit plan` with the same exclusions.
Pool availability comes from the pinned catalog: 20 mainnet and nine Sepolia
pools. Four mainnet cDAI pools are excluded. Use the catalog rather than
assuming arbitrary pool addresses or denominations are accepted.

Independent random notes are the default. Adding `--seed-bundle` to either
creation command generates a fresh 24-word mnemonic session with recoverable
note derivation and raw notes in the backup. This is not an existing-mnemonic
import command. Preserve the complete backup, including its session metadata;
neither note creation nor invoice creation deposits funds.

## Deposit notes or pay an invoice

```sh
lake exe tornado deposit send --notes-file ./notes.txt --key-file ./owner-key.txt --chain 1 --dry-run
lake exe tornado deposit send --notes-file ./notes.txt --key-file ./owner-key.txt --chain 1 --broadcast
```

`deposit send` accepts 1–100 notes of one asset; denominations may differ.
Review the sender, network, targets, commitments, total value and gas before
signing. A single note defaults to ordinary EIP-1559 transactions, even if
the sender already has a compatible delegation. ERC-20 deposits may require
reset/approval transactions before their deposit.

Multiple notes use Simple7702 batches for an undelegated EOA or the exact
pinned compatible delegation. Other sender code defaults to sequential
transactions. `--sequential` forces ordinary transactions. `--delegated`
forces batching, including for a single note, and explicitly replaces a
different valid EIP-7702 delegation; ordinary contract code is rejected.
The two flags conflict. Delegation persists even if later deposits are
cancelled, and its signed authorization can reach estimation before deposit
submission. Batch chunks contain at most 12 ETH or five token notes.

Sequential transactions have a two-million gas limit including estimation
headroom and a 0.02 ETH maximum gas-cost cap. ETH notes above 0.01 ETH also
have a 10% value cap. Delegated batches have 15 million call gas, 16 million
total gas and a 0.05 ETH maximum network-cost cap. ETH batches containing a
note above 0.01 ETH retain the 10% value cap. Bundler acceptance is not assured
merely because a batch fits these local limits.

For a new send, `--journal` is optional. Otherwise the CLI prints a unique
private `tornado-deposit-<chainId>-<random>.json` filename in the current
directory. Keep that file. Dry-run creates no journal. An existing lock,
commitment claim or journal is not permission to delete it; use
[recovery and reconciliation](RECOVERY.md).

An invoice contains public funding commitments rather than spendable note
secrets. Save the output of `notes invoice` as the payer's invoice file, then:

```sh
lake exe tornado deposit pay-invoice --invoice-file ./invoice.json --key-file ./owner-key.txt --chain 1 --dry-run
lake exe tornado deposit pay-invoice --invoice-file ./invoice.json --key-file ./owner-key.txt --chain 1 --broadcast
lake exe tornado deposit status --journal ./deposit-journal.json
```

Invoice payment uses sequential transactions. Confirm through a trusted
channel that the recipient retained the corresponding secret. Self-funded
delegated deposits can leave unused ETH as EntryPoint gas credit under the
sender EOA. It can fund future UserOperation gas, not deposit principal or
ordinary transactions. The CLI reports this credit; its recovery is distinct
from a withdrawal smart-account sweep. See [recovery](RECOVERY.md).

## Withdraw one note

```sh
lake exe tornado withdraw one --note-file ./notes.txt --note-index 1 --recipient 0xRecipient --chain 1 --dry-run
lake exe tornado withdraw one --note-file ./notes.txt --note-index 1 --recipient 0xRecipient --chain 1 --preflight
lake exe tornado withdraw one --note-file ./notes.txt --note-index 1 --recipient 0xRecipient --chain 1 --broadcast
```

Replace `0xRecipient` with the intended address. `--note-index` is 1-based and
required when selecting one note from a multi-note backup. Local dry-run makes
no network call, proof or status file. Preflight adds read-only history and
spent checks. Those queries disclose the selected note's nullifier hash to
the RPC and may link deposit and withdrawal activity.

The default `--route 4337` uses the configured paymaster/bundler and derives a
temporary signing key from the note, including for independently generated
notes. `--route relayer` instead submits through a registered Classic relayer;
it supports original Tornado pools only. A relayer fee must be positive,
below the note value and at most 20% of it. Conservative registration, ASCII
ENS/DNS, stake, queue and fee checks can exclude otherwise usable relayers.

Both routes reserve the same per-note status path within `--status-dir`.
Changing route or directory must not be used to bypass an uncertain attempt.
Classic-relayer status uses chain evidence, not `v1/jobs` progress or a
relayer-reported failure. Missing job IDs and ambiguous responses remain
unknown; they do not permit a second proof submission.

## Batch withdrawals and contract calls

```sh
lake exe tornado withdraw batch --notes-file ./notes.txt --owner-key-file ./owner-key.txt --recipient 0xRecipient --chain 1 --dry-run
lake exe tornado withdraw batch --notes-file ./notes.txt --owner-key-file ./owner-key.txt --recipient 0xRecipient --chain 1 --broadcast
```

Batch mode accepts 2–12 same-asset notes, or 1–12 when contract calls are
present. It derives and checks the owner's recoverable SimpleAccount.
Omitting `--recipient` leaves proceeds in that account. Without custom calls,
an external `--recipient` (`--receiver` alias) forwards the sum of selected
denominations minus the sponsoring note fee. Conditional unused-fee refunds
can still arrive in the smart account. `--note-file` aliases `--notes-file`.

Use `--contract-calls <file>` for ordered raw call JSON or a Safe Transaction
Builder v1.0 file. Only ordinary `CALL` operations are accepted: at most 12
calls, 16 KiB calldata each and 64 KiB total. Calls to the smart account itself
are blocked. An external receiver cannot be combined with custom calls.
Supported imported ABI types include bounded integers, addresses, booleans,
bytes, strings, tuples and arrays; nesting is limited to 12 and arrays/tuples
to 1,024 entries. Review target, ETH value and calldata for every action.

Batch dry-run checks account identity over RPC but makes no proof, signature,
journal or submission. Gas estimation uses dummy payloads before real proving.
After proving, the CLI rechecks history, account and gas conditions before a
five-minute final review. Eligible withdrawals may lower their gas bid before
review without changing proofs, note fees or payouts; custom calls retain
their original bid. A stale or excessive quote stops preparation.

Batch submission runs one signed final simulation. Its RPC receives an
executable operation and could relay it. The default
`--simulation-policy required` blocks unavailable or failed simulation;
`best-effort` allows only narrowly classified unavailability, never a known
failure. Direct one-note withdrawals do not run this batch execution
simulation. A specific zero-execution bundler estimator incompatibility is
handled automatically for direct withdrawals only; batches still require a
successful estimate. See [security specification](SECURITY_SPEC.md).

The sponsor is withdrawn during paymaster validation. Later execution failure
does not mean that note is unspent or every effect was rolled back. Reconcile
the original attempt and inspect its smart account before taking further
action. Do not blindly retry. See [recovery](RECOVERY.md).

## History, status and resource limits

```sh
lake exe tornado history --note-file ./notes.txt --note-index 1 --chain 1
lake exe tornado compliance report --note-file ./notes.txt --note-index 1 --chain 1 --out ./report.json
lake exe tornado withdraw status --status-file ./withdrawal-status.json
lake exe tornado smart-account show --owner 0xOwner --chain 1
```

History and preflight validate selected pool history and exact receipt/event
evidence. A compliance report is a new private, redacted file, but it still
links the deposit to its operator. RPC evidence is not consensus verification.
Senders proceed after one validated inclusion; reorganization remains possible.
Status commands reconcile existing evidence without creating a replacement.

`--assets-dir` names a directory containing pinned `history/` snapshots;
`--proving-assets-root` selects the root containing bundled proving/witness
assets. Missing proving assets are not downloaded automatically. An optional
`--history-cache-dir` must already be private, owned by the user, mode `0700`
and free of access-granting ACLs. Accepted caches are rechecked against RPC
checkpoints; they do not independently authorize spending.

History has a five-minute aggregate budget, at most 4,096 RPC requests,
256 MiB transferred bytes, one million events and two million freshly scanned
RPC blocks. Oversized, incomplete or inconsistent history stops preparation.
An RPC unable to serve an old checkpoint can force a slower rebuild; an old
pool may need another RPC with historical state or usable pinned snapshots.
For interrupted sends, stale files or uncertain status, follow
[recovery](RECOVERY.md) rather than deleting reservations.
