# CLI parity and safety register

Target: clean `tornado-cli-new-era` main commit `daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7`, `@kohaku-eth/tornado-cash@0.1.0-alpha.38`, and pinned TypeScript build SHA-256 `cb039416616458ab261036e08e3c4d83991a1b6d7ab4259328894292c035f809`. This register describes implementation coverage. It is not a correctness certificate.

## Seventeen TypeScript leaf commands

- `pools` and `deposit plan`: native catalog, amount parsing, and planning. The 156-case CLI suite compares these commands and root version flags with the pinned TypeScript build.
- `notes create` and `notes create-plan`: native entropy, independent or seeded note derivation, and exclusive protected backup creation. Compatibility and recovery tests are finite; the secret-handling code is not production certified.
- `notes inspect` and `notes invoice`: native protected backup read and public commitment/invoice derivation. Six pinned note-file parity and rejection cases pass.
- `deposit send`: native dry-run and explicit `--experimental-send --journal <new-path>`. A protected 1–100-note backup selects sequential EIP-1559 or Simple7702 batching; `--sequential` forces ordinary transactions. Protected native signing, shared sender locks and commitment claims, exact approvals, journal-before-exposure, post-review rechecks, exact receipts/events and twelve confirmations are connected. Simple7702 also records its signed persistent delegation before estimation. Offline fault tests and viem vectors pass; funded testing and end-to-end proofs remain open.
- `deposit pay-invoice`: native `--dry-run` and `--experimental-send --journal <new-path>`. The live path signs sequential EIP-1559 transactions through a protected native libsecp256k1 boundary, creates a local per-invoice claim and per-sender lock, records each signed transaction hash in a protected journal before broadcast, asks the user to type `SEND` for each transaction, enforces a conservative gas-cost ceiling, stops on ambiguous outcomes, and checks exact successful Deposit events plus 12 confirmations. It has injected fault and pinned signature tests but no funded live test or end-to-end proof. It does not accept `--yes`.
- `deposit status`: native sequential and Simple7702 batch journal reconciliation. Exact receipt, EntryPoint and Deposit events gate confirmation; a protected byte-for-byte compare-and-replace updates the journal. A separate `deposit inspect-status` command reads sequential journals without updating them.
- `withdraw one`: native local `--dry-run`, history `--preflight`, and explicit `--experimental-send --route 4337|relayer`. The parent obtains public metadata/history and a bound proof from the separate Lean worker; direct 4337 note-derived signing also stays in that worker. Both live routes require typed `WITHDRAW` and reject `--yes` or replacement retries. Before executable exposure, they reserve the same protected opaque per-note status path, so changing route within the same status directory cannot bypass an attempt. The spent query discloses the nullifier hash to the selected RPC. One-note 4337 journals before its single bundler send and does not run the batch execution simulation; Classic relayer makes exactly one proof POST and preserves an unknown result without retry.
- `withdraw batch`: native dry-run and explicit experimental 4337 submission for 2–12 same-asset notes, or 1–12 with contract calls. It checks a locally predicted pinned smart account, optional receiver, protected owner key, shared sender lock, ordered raw/Safe calls and all selected notes. Native `contractMethod` re-encoding supports bounded Solidity primitives, tuples and arrays, with 28 viem encoding/hash cases and 20 rejection cases. Sponsored proof/quote construction, typed `WITHDRAW`, protected per-note reservations, signed simulation and one-send execution are connected. Unknown or partially persisted outcomes retain candidate evidence and block replacement.
- `withdraw status`: native one-note 4337, Classic relayer, and batch-4337 journal reconciliation. One-note status checks exact EntryPoint and pool events and updates its protected journal. Relayer status confirms only from exact chain receipt/pool events; relayer job-only claims remain unknown. Batch status validates all mirrors before updating, retains every candidate/reservation and uses an authoritative in-progress marker plus protected mirror CAS. Partial writes remain recoverable and report exit 2 instead of claiming completion.
- `smart-account show`: native pinned-account identity and balances at one RPC block, tested with offline fixtures.
- `smart-account status`: native protected recovery-journal reconciliation, exact transaction/receipt checks and protected compare-and-replace updates.
- `smart-account recover`: native dry-run accepts a public owner or protected owner-key-file. Live recovery requires `--experimental-send --owner-key-file <path> --journal <new-path>` and typed `RECOVER`; it does not accept `--yes`. It checks the locally predicted pinned account and supported balances, rechecks the exact review after approval, enforces bounded gas/fees, signs through the protected native key boundary, and journals the exact zero-value type-2 transaction before broadcast. It shares the owner sender lock with deposit/batch-withdrawal routes, retains it after uncertain signing/send outcomes, and releases it only after exact transaction/receipt evidence and twelve observed confirmations.
- `history` and `compliance report`: native bounded Saga/RPC history, pinned `--assets-dir` imports, optional protected chunk caches, checkpoint/root/count checks and reorg handling, exact-block pool logs and receipts, and redacted protected reports. Withdrawal preflight accepts the same assets/cache options. Ethereum consensus/finality remains an assumption.

All 17 command names have a native route, including experimental deposit, withdrawal and recovery sends. This is not full CLI/dependency parity or a correctness certificate. Option/resource bounds, incomplete secret hardening, external state assumptions and unproved effectful behavior remain. Verification uses public unfunded fixtures and injected submission effects. Live routes require `--experimental-send`; that flag does not establish production safety.

## Known compatibility differences

All primary deposit, withdrawal and recovery flows are connected experimentally,
but these concrete behavior differences remain in addition to proof gaps:

- Live sends require typed review (`SEND`, `WITHDRAW` or `RECOVER`) and do not
  support unattended `--yes`. Live withdrawal routes also reject the legacy
  `--retry-rejected` replacement option; existing attempts must be reconciled.
- Native `--assets-dir` selects history assets only. Proving uses the bundled
  `assets/proving` and witness assets under `--proving-assets-root`. This differs
  from the TypeScript unified artifact directory and automatic remote artifact
  fallback; the native command does not reproduce that artifact-loading workflow.
- Relayer discovery history is scanned through bounded RPC requests rather
  than imported from the pinned relayer-history chunks. Supported ranges and
  provider limits can therefore affect availability differently.
- Native relayer withdrawal status uses chain evidence and preserves the saved
  job ID. It does not fetch `v1/jobs` progress, relayer-reported `FAILED` state,
  or transaction-hash hints. A pending/failed job visible in the TypeScript
  interface may remain unknown here until matching chain evidence is found.
- Relayer ENS names and origins use a conservative ASCII/DNS subset. Unicode
  names, explicit ports and IP-literal origins are rejected; the TypeScript
  parsers accept a wider input domain.

These limits affect interactivity, accepted inputs, loading and status behavior.
They are not resolved merely by adding more proofs over the current code.

## What the current checks establish

`node scripts/verify.mjs` rebuilds the native modules, rejects undeclared axioms and proof escapes, checks the exact C extern allowlist, runs finite crypto/protocol vectors and OS-boundary fault tests, and compares the supported catalog/planner/note-file surface with the pinned TypeScript CLI. The full gate must be rerun after every implementation change; an older `reports/verify.json` is not evidence for current source.

Lean theorems constrain selected pure native definitions: catalog facts, ABI/transaction encodings, event matching, fee arithmetic, planner conservation, policy transitions, and abstract effect ordering. Read-only differential coverage is 156 catalog/planner/version cases plus six note-file cases. Connected send engines have focused offline compatibility and injected fault tests; they do not yet have a theorem showing their actual C/HTTPS execution traces refine the policy model. Exact source parity and theorems over pure helpers cannot establish whole-program correctness on their own.

An internal one-note proof-to-call builder joins a protected note, selected-pool history, exact-block root/leaf/spent checks, authenticated proving assets, fresh blinding, and Classic calldata. A public unfunded fixture matched the pinned SDK's 256-byte proof and call encoding in about 194 seconds. Runnable commands instead use the isolated worker/session route; neither prover route has constant-time or secure-erasure guarantees.

The separate [Classic prover worker](PROVER_WORKER_SCOPE.md) moves note reading, proof generation and direct note-derived signing into a child process. The parent sends only canonical public inputs, caps the response, checks request hashes and all six signals, verifies proofs against the compiled Classic key, and builds bound calldata. Experimental commands use the sibling executable. Public unfunded fixtures exercise real proof generation. Process isolation does not make its Lean-managed witness and variable-time arithmetic secret safe, and the executable's installation is trusted rather than authenticated by Lean.

`PaymasterPrepare` uses dummy proofs/signatures/authorizations during bounded estimation, checks chain fee references and token quotes, then obtains each real proof once after convergence. `SponsoredWithdrawal` binds the sponsor, zero-fee remaining notes, recoverable account, receiver, and exact ordered contract calls. After slow proving, the live adapter rechecks selected history/known roots, account identity/nonce and fresh host gas-price bounds before starting the five-minute review window; it checks them again after approval without silently changing the reviewed fee or proof. `WithdrawalSend` joins final review, signature, protected reservation, exposure marking and one send. Batch mode additionally runs signed final simulation, which is executable exposure because its RPC can relay the operation. Direct one-note mode does not run that execution simulation. Explicit batch simulation failures block; the default `required` policy blocks unavailability too. Opt-in `best-effort` admits only narrowly identified unavailability after successful dummy estimation, never a known failure or repeated simulation. The public worker fixture checks a real nonzero-fee sponsor proof and a second pinned SDK proof.

The sponsor note is withdrawn during paymaster validation. Batch execution
failure does not establish that it remains unspent or that all effects rolled
back atomically. Funds may remain in the recoverable account. Reconcile the
original candidate, inspect `smart-account show`, and use reviewed recovery
instead of replacing a failed UserOperation blindly. Success requires all
expected events; standalone status is observed inclusion, not finality.

Classic relayer discovery, registration/stake/status/fee checks, verified proof binding and one-POST execution are connected. Revalidation follows typed approval, and an exclusive permanent per-note claim precedes POST. Lost responses, missing job IDs, partial journal writes and ambiguous status never trigger a second POST. A job response alone cannot establish confirmation; matching pool receipt/event evidence is required. Relayer status currently reports observed inclusion without a twelve-block wait; sponsored and recovery sends use twelve observed confirmations before owner-lock release. Neither is authenticated finality.

The HTTPS RPC, Saga proxy, bundler, relayer, C/POSIX and libsecp256k1 boundaries, disk hardware, worker installation, Ethereum finality, deployed pool/verifier code, and cryptographic hardness are external assumptions. Malformed or inconsistent API data fails closed within explicit bounds; an internally consistent malicious RPC can still lie. Chain IDs, block hashes, receipts and event checks do not establish truth without consensus-state authentication.

The fund-safety specification requires exact reviewed intent before signing,
reservation before executable exposure, no duplicate/replacement under
uncertainty, and success only from exact transaction/event evidence. Selected
policy and replay theorems establish parts of these properties; complete
runnable command refinement remains unproved. Constant-time/zeroizing note
handling, authenticated worker and deployed-code binding, exhaustive provider
fault coverage and funded testnet validation are outside current coverage.
The variable-time, nonzeroizing worker has no production security guarantee.
