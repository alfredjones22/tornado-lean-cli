# Tornado CLI in Lean

MIT licensed. Copyright (c) 2026 Tornado. See [LICENSE](LICENSE).
Vendored dependencies and reference fixtures retain their original license notices.

> **Best-effort formal verification does not guarantee bug-free code or prevent every loss of funds. This is experimental software, not a certified wallet.** Native deposit, one-note 4337/Classic-relayer withdrawal, smart-account batch withdrawal with optional contract calls, and recovery send routes require explicit `--experimental-send` and typed approval. Verification uses public, unfunded fixtures and injected submission effects. Full CLI/dependency parity and end-to-end correctness are not proved. The isolated native Lean note prover and note-derived signer are variable-time and do not guarantee secret erasure.

This directory contains the runnable Lean executable, its native libraries, specifications, proofs, compatibility vectors, and verification scripts. It targets clean `tornado-cli-new-era` commit `a24d5f5e89d1f2486a031b1e5e8b1a92e81e1326` with `@kohaku-eth/tornado-cash@0.1.0-alpha.40`. The oracle identity pins the lockfile and installed package bytes as well as the externalized CLI build in `fixtures/typescript-oracle-identity.json`. Lean is pinned to `leanprover/lean4:v4.29.1`.

Start with the [withdrawal security specification](docs/WITHDRAWAL_SECURITY_SPEC.md) to review the user-facing rules, their executable definitions, and their assumptions. It distinguishes reviewed-intent and exposure guarantees, worker disclosure confinement, sampler distributions, conditional native verifier completeness and proof-output privacy, and the remaining physical-process, chain and cryptographic assumptions. **The configured history RPC is trusted with deposit–withdrawal linkage:** it can correlate selected deposit receipt queries with selected nullifier-spent queries.

The [security contracts](docs/SECURITY_CONTRACTS.md) state the intended batch, backup, recovery and disclosure properties independently of their encoders and checks. [Verification instructions](docs/VERIFICATION.md) distinguish the kernel-only gate from full regression evidence and describe the [local Solidity/EVM checks](docs/LOCAL_EVM_SCOPE.md).

The reusable [LeanCrypto package](packages/lean-crypto/README.md) has no external
Lake dependencies. The separate [mathematical proof workspace](proofs/README.md)
uses pinned Mathlib; the CLI and pure runtime library do not import Mathlib.

## Build and run

The [reservation and restart scope](docs/RESERVATION_RECOVERY_SCOPE.md) explains
the runtime-used journal certificates, partial-write handling and conditional
readmission guarantees, including what concurrent starts can still do.

```sh
lake build tornado tornado_prover_worker
lake exe tornado --help
lake exe tornado pools --chain 1 --asset ETH
lake exe tornado deposit plan --chain 1 --asset ETH --amount 1.4
lake exe tornado notes create --denom 0.01 --count 2 --out /absolute/path/to/new-private-backup
lake exe tornado notes inspect --file /absolute/path/to/private-backup
lake exe tornado notes invoice --file /absolute/path/to/private-backup
lake exe tornado deposit send --notes-file /absolute/path/to/private-backup --key-file /absolute/path/to/private-key --dry-run
lake exe tornado deposit pay-invoice --invoice-file /absolute/path/to/public-invoice --key-file /absolute/path/to/private-key --dry-run
lake exe tornado deposit status --journal /absolute/path/to/deposit-journal
lake exe tornado withdraw one --note-file /absolute/path/to/private-backup --recipient 0xRecipient --dry-run
lake exe tornado withdraw batch --notes-file /absolute/path/to/private-backup --owner-key-file /absolute/path/to/private-key --dry-run
lake exe tornado withdraw status --status-file /absolute/path/to/withdrawal-status
lake exe tornado history --note-file /absolute/path/to/private-backup
lake exe tornado smart-account show --owner 0xYourEOAAddress --chain 1
lake exe tornado smart-account status --journal /absolute/path/to/recovery-journal
lake exe tornado smart-account recover --owner 0xYourEOAAddress --dry-run
lake exe tornado deposit inspect-status --journal /absolute/path/to/sequential-journal
```

The command logic, protocol parsing, proof code, and reference cryptography are Lean. Trusted native boundaries provide protected POSIX file access, authenticated HTTPS via system libcurl, and one-shot protected-key signing with [pinned libsecp256k1](native/vendor/libsecp256k1/UPSTREAM.md). These components are not proved Lean code. The executable does not shell out to the TypeScript CLI. The `scripts/` directory uses Node for development checks and TypeScript parity. The [command matrix](docs/PARITY_MATRIX.md) records all 17 TypeScript leaf commands and current coverage.

All primary fund flows are connected experimentally, with concrete
[compatibility differences](docs/PARITY_MATRIX.md#known-compatibility-differences):
typed review replaces unattended approval/replacement flags, artifact loading
differs, and relayer history, status progress and accepted origins are narrower.
This is not full behavioral parity with the TypeScript CLI.

Explicit local development RPCs may use HTTP on `127.0.0.1`, `localhost` or
`[::1]`. Both URL spelling and the actual socket destination must be loopback.
Remote plaintext, redirects, URL credentials and ambient proxies are rejected.

Protected owner-key signing reads a key file only inside the native signer boundary, reloads it after approval, and checks its public address against the reviewed sender. Dry-run owner-address lookups use the same boundary. Note creation and isolated withdrawal proving still create Lean-managed secret copies; the whole CLI is not zeroizing or side-channel certified. See the [deposit sender scope](docs/DEPOSIT_SEND_SCOPE.md) and [native signer boundary](docs/NATIVE_SIGNER_BOUNDARY.md).

The [separate Classic prover worker](docs/PROVER_WORKER_SCOPE.md) reads protected notes in its own process, exposes bounded public metadata, and generates a proof bound to reviewed public inputs. The parent verifies the proof against the compiled Classic key before building calldata. The worker also handles note-derived signing for direct 4337 withdrawals. It is connected to experimental commands; proof-generation tests use public, unfunded fixtures. Process isolation does not provide constant-time execution, secure erasure, or executable authentication. The sibling worker executable and its installation remain trusted.

## What is implemented

- Static native Lean catalog of 29 SDK-supported mainnet and Sepolia pools, exact decimal amount parsing, exclusions, denomination planning, and a runtime check that every printed plan conserves the requested amount and has consistent note/batch counts.
- Native Lean Keccak-256, SHA-256/HMAC-SHA256, SHA-512/HMAC-SHA512, BLAKE-256, BabyJubJub Pedersen, MiMC sponge, and MiMC Merkle tree code, with pinned compatibility vectors. English BIP39, hardened BIP32, reference secp256k1 deterministic low-S signing, Ethereum address derivation, and the SDK's EIP-712 seeded-note derivation are present. Native raw-note parsing, commitment/nullifier recovery, public invoices, Classic/ERC-20/SimpleAccount ABI, EntryPoint v0.8 UserOperation hashes, EIP-1559 RLP, EIP-7702 authorization hashing, and strict deposit/withdrawal/EntryPoint event decoding are present. Protected owner-key routes sign through the native C boundary; serialization remains Lean.
- The exact pinned compressed circuit and proving key are bundled under [`assets/proving/`](assets/proving/README.md). Lean computes all 36,528 signals and all 28,300 R1CS witness slots for the pinned Tornado circuit, authenticates the decoded constraints, and checks all 28,275 equations. Four public full-witness cases pass, including a rightmost Merkle path. Lean also authenticates and parses every proving-key section, including all A/B polynomials and G1/G2 query points; see [key scope](docs/PROVING_KEY_SCOPE.md). A public full-size proof fixture is assembled below; this is not a secret-safe production prover. See [native witness scope](docs/WITNESS_VM_SCOPE.md) and [proving scope](docs/GROTH16_SCOPE.md).
- A native Lean [gzip/DEFLATE decoder](docs/GZIP_SCOPE.md) authenticates and decompresses both pinned proving assets, with output limits, CRC/ISIZE checks, a block-count cap, and finite format vectors. This removes runtime reliance on Node or zlib for the compressed assets; the OS file read remains trusted.
- Native BN254 field towers, G1/G2 groups and scalar/MSM loops, normalization and reduced Tate pairing are used by the isolated prover. The proof workspace certifies their source-level mathematical meanings, bilinearity and a nontrivial generator result. Honest setup/key spans and finite-output conditions yield native verifier completeness and scalar-equation equivalence. Arithmetic remains variable time and nonzeroizing; see the [mathematical scope](proofs/README.md).
- Native NQR-7 FFT/IFFT and sparse A/B-to-H derivation have complete transform, roundtrip, convolution, strict H-dimension and QAP-quotient construction proofs under their stated original-row conditions, plus independent finite oracle vectors. See [FFT scope](docs/FR_FFT_SCOPE.md).
- Native BN254 G1/G2 windowed MSM and Groth16 point assembly pass finite noble vectors. A compositional [Classic proof pipeline](docs/CLASSIC_PROOF_PIPELINE_SCOPE.md) joins authenticated compressed assets, the complete checked witness, H, proof points and compiled-key verification. Its public, unfunded fixture emits the exact 256 Solidity proof bytes of the pinned SDK oracle. A separate native reduced Tate [pairing verifier](docs/BN254_PAIRING_STATUS.md) accepts that public proof and rejects changes to each public signal. A [compiled Classic key](docs/CLASSIC_KEY_SCOPE.md) contains all verifier points from immutable source, without runtime JSON key substitution. The connected experimental prover uses variable-time arithmetic and retains secret intermediates in process memory. See [MSM scope](docs/GROTH16_MSM_SCOPE.md).
- A [Groth16 blinding sampler](docs/PROOF_BLINDING_SCOPE.md) uses separate kernel CSPRNG reads and bounded rejection sampling for nonzero canonical Fr values. Deterministic SDK comparison fixtures use fixed test blinding; the connected worker samples fresh values. Production secret safety and deployed pool/verifier binding are still open.
- An internal [one-note withdrawal builder](docs/WITHDRAW_PROOF_SCOPE.md) composes a protected selected note, bounded pool history, exact-block root/leaf/spent checks, authenticated proving assets, fresh blinding, a complete native Classic proof, and direct/paymaster/relayer calldata binding. One unfunded public fixture matched the pinned SDK proof bytes and direct calldata in about 194 seconds. Runnable experimental commands use the separate worker/session path instead of importing note secrets into this parent-side builder.
- `smart-account show` reads one RPC block and validates the pinned account identity before displaying public balances. Its offline request, response, and output tests pass; no live RPC parity run or consensus authentication has been completed. See [show scope](docs/SMART_ACCOUNT_SHOW_SCOPE.md).
- `smart-account status` reconciles a protected recovery journal against the exact recorded zero-value type-2 transaction and receipt, then updates it through protected compare-and-replace. See [status scope](docs/SMART_ACCOUNT_STATUS_SCOPE.md).
- `smart-account recover --dry-run` reviews pinned account identity and supported balances. Its experimental send mode requires a protected owner key, new journal, shared sender lock and typed `RECOVER`. It rechecks the same account/balances/calls after approval, signs only the bound zero-value owner transaction, journals before broadcast, and waits for exact inclusion plus twelve observed confirmations. Unknown outcomes retain the lock and journal. See [scope](docs/SMART_ACCOUNT_RECOVER_SCOPE.md).
- `deposit send --dry-run` previews sequential or Simple7702 calls for up to 100 protected notes. Its explicit experimental send mode connects protected native signing, exact approvals, journals, shared sender locks and commitment claims, post-review rechecks, exact indexed transactions/events, and twelve confirmations. Simple7702 records the signed persistent delegation before estimation can receive it. `deposit pay-invoice` offers the corresponding one-invoice dry-run and experimental sequential send. Fault tests and pinned viem vectors cover both engines; funded end-to-end tests and correctness proofs remain open. See [multi-note scope](docs/DEPOSIT_MULTI_SCOPE.md) and [invoice scope](docs/DEPOSIT_SEND_SCOPE.md).
- `deposit status` compares sequential or 7702 batch journals with chain receipts and exact pool events, then updates the protected file through a native compare-and-replace boundary. The extra `deposit inspect-status` command only reads sequential journals. See [status scope](docs/DEPOSIT_STATUS_COMMAND_SCOPE.md) and [inspector scope](docs/DEPOSIT_STATUS_SCOPE.md).
- `withdraw one` supports local `--dry-run`, read-only history `--preflight`, and explicit `--experimental-send --route 4337|relayer`. Live routes require typed `WITHDRAW`, reject `--yes` and replacement retries, keep note secrets in the separate worker, and exclusively reserve the same opaque per-note status path across routes before exposing executable material. Relayer submission makes one proof POST and confirms only from exact pool receipt/event evidence; a relayer job alone never confirms. See [one-note scope](docs/WITHDRAW_ONE_SCOPE.md) and [relayer scope](docs/RELAYER_QUOTE_SCOPE.md).
- `withdraw batch` supports dry-run and experimental smart-account sending for multiple notes, or a single note with post-withdrawal calls. Protected owner signing, a shared sender lock, pinned account checks and ordered raw/Safe calls are connected. Native `contractMethod` imports support bounded integers, addresses, booleans, bytes, strings, tuples and arrays, and reject calldata disagreements. See [batch scope](docs/WITHDRAW_BATCH_SCOPE.md).
- Sponsored withdrawal estimation uses dummy proofs/signatures/authorizations and bounded gas refinement. Real proofs are generated after the quote stabilizes; selected history/known roots, account state and current host fee bounds are rechecked after slow proof generation before the five-minute final review window starts, and again after approval. All signed operations are journaled and marked exposed before the one bundler send. Batch mode first runs final signed `eth_simulateV1`; its RPC can relay the operation. Explicit simulation failures block. The default `required` policy also blocks unavailability; opt-in `best-effort` allows only narrowly classified unavailability after successful dummy estimation. Batch simulation is attempted at most once. Direct one-note mode does not run this execution simulation.
- A batch's sponsoring note is withdrawn during paymaster validation. A failed execution therefore does not imply an unspent note or an atomic rollback of the whole batch; funds may remain in the recoverable smart account. Reconcile the original candidate and inspect `smart-account show`/`smart-account recover` rather than starting a replacement because the UserOperation failed. Successful status requires every expected event; standalone status reports observed receipt inclusion, while send adapters additionally wait for twelve observed confirmations.
- `withdraw status` reconciles one-note 4337, Classic relayer and batch-4337 journals with exact receipts/events. Batch updates preserve every candidate across protected mirror CAS writes and an authoritative in-progress marker. Partial updates and unknown outcomes retain reservations and report uncertainty. Sponsored send commands wait for twelve observed confirmations before releasing their owner lock; relayer status is receipt inclusion, without that depth wait. See [one-note status](docs/WITHDRAWAL_STATUS_COMMAND_SCOPE.md), [relayer status](docs/RELAYER_WITHDRAWAL_STATUS_SCOPE.md), and [batch status](docs/BATCH_WITHDRAWAL_STATUS_SCOPE.md).
- `history` and `compliance report` reconstruct a selected note's bounded pool history and check exact-block receipts; the report is a new protected redacted JSON file. The `isSpent(bytes32)` query discloses the selected note's nullifier hash to the RPC and can link a later withdrawal. See [scope](docs/HISTORY_COMMAND_SCOPE.md).
- Native typed EIP-1559/7702 serialization and decoding, an additional EIP-7702 consensus/intent gate, deterministic smart-account recovery call construction, typed JSON-RPC envelopes, and transaction-bound receipt parsing. These are finite compatibility tests and selected Lean theorems, not a complete chain client.
- Native [Saga and RPC validators](docs/native-history-scope.md), the [history reducer](docs/HISTORY_REDUCER_SCOPE.md) and [fetch orchestrator](docs/HISTORY_SYNC_SCOPE.md) serve history, reports and withdrawal preflight. [Pinned offline history and protected caches](docs/HISTORY_SNAPSHOT_SCOPE.md) add `--assets-dir` and `--history-cache-dir`, chunk integrity, checkpoint/root/count checks and reorg handling. An RPC can still omit or fabricate data, and resource limits are narrower than unconstrained API responses.
- Native pure safety-policy cores for simulation admission, relayer fee arithmetic, one-note and batch signing/reservation/submission transitions, and status validation. Independent specifications and abstract effect traces prove selected reservation-before-exposure, one-send, unknown-outcome, and exact-evidence properties. Those policy models are not yet end-to-end refinement proofs of every runnable command. The experimental invoice engine has concrete fault tests for its own effect order.
- Protected private-file creation/read/compare-and-replace and HTTPS POST/GET OS bindings are implemented and tested. `notes create` and `notes create-plan` sample OS entropy, derive independent or fresh 24-word seeded notes in Lean, and write a new private backup exclusively. `notes inspect` and `notes invoice` read through that adapter, then compute public commitments/invoices in Lean. Regression tests reject inherited and direct macOS ACL grants. Actual disk durability, TLS roots, and RPC truth are trusted boundaries, not Lean theorems.
- A bounded append-only [attempt journal](docs/ATTEMPT_JOURNAL_SCOPE.md) records immutable one-note and batch transition intents through protected file creation and replays them on restart. A [concrete replay refinement](docs/JOURNAL_IO_REFINEMENT_SCOPE.md) checks reservation and one-send gates and has write-failure, race and crash tests. A separate [per-note claim wrapper](docs/NOTE_CLAIMS_SCOPE.md) exclusively reserves nullifiers within one private local instance root, including concurrent-process tests. These components are not yet the journal used by the experimental invoice sender and do not provide a full proof of its effects.

With Node 22.18 or newer, `node scripts/verify.mjs` builds the project, rejects proof escapes and undeclared axioms, checks the exact native FFI allowlist, runs crypto/parser/planner/witness and OS-boundary tests, and compares the supported read-only commands with the pinned TypeScript CLI: 156 catalog/planner/version cases plus six note-file cases. It also checks newly generated independent and seeded backups, including seed-session recovery against the pinned SDK. It writes a [machine report](reports/verify.json) with **PASS_WITH_LIMITATIONS** only when every current check passes. The local TypeScript checkout is needed for the parity oracle but not to run the Lean executable.

## Meaning of the proofs

The [proof scope](docs/PROOF_SCOPE.md) distinguishes acceptance rules,
construction results, mathematical representation and finite tests. The
sponsored runner uses its proved command machine, and the worker uses a
restricted effect program with a typed release gate. A successful Classic
pipeline result now carries exact provenance from the original assets,
withdrawal input and supplied blinding through witness generation, H, point
assembly and serialization. This proves which native computations produced
a returned result; it does not prove that every valid input succeeds.

The [mathematical workspace](proofs/README.md) proves the actual field towers,
complete FFT/IFFT and H/QAP construction, G1/G2 groups and MSMs, full native
A/B/C assembly, exact byte encoding, reduced Tate bilinearity and a closed
nontrivial generator-pair certificate. Native verifier acceptance is derived
from original source equations and explicit honest setup/key relations, with
the executable's finite-point conditions.

The [application workspace](app-proofs/README.md) connects the actual worker
program, byte sampler, proof assembly, acceptance, wire validator and terminal
output. Under its explicit source/admission and honest-setup hypotheses, two
valid source contexts with the same public setup and signals differ on every
stdout/stderr/exit-status event by at most `2^-251`. All later proof failures
and sampler exhaustion remain in that distribution. This is a conditional
statistical output theorem; timing, memory, physical IO and other worker
modes' cryptographic contents are outside it.

Read-only parity remains bounded to the documented catalog/planner/version
and note-file cases. Complete command refinement, cryptographic hardness,
setup honesty, SHA/DEFLATE specifications, C/OS behavior, physical durability,
RPC truth and deployed-contract behavior remain outside the established
results. Compatibility vectors are finite tests. [Build provenance](docs/BUILD_PROVENANCE.md)
checks byte identity against an independently trusted manifest; it does not
authenticate that manifest or pin the worker used at runtime.

The fund-safety specification is: sign only the exact reviewed recipient, pool, amount, fee and ordered actions; preserve a claim before exposing anything executable; never create a duplicate or replacement while an outcome is uncertain; and report success only from matching transaction and event evidence. Native Lean provides definitions and proof-carrying validators for these rules, and selected policy/replay theorems establish parts of them. There is no complete proof that every effectful command follows those rules across actual files, processes and network failures.

External APIs may return arbitrary data. Bounded parsers and exact binding checks reject malformed or inconsistent responses, but an internally consistent lie can pass. Without authenticating Ethereum consensus state, the meaningful guarantee is conditional on truthful chain evidence, the expected deployed contracts, sound cryptography, and the trusted OS/native boundaries. Twelve RPC-observed confirmations are a consistency/depth policy, not a consensus proof. Secret erasure and side-channel safety, authenticated worker installation and chain state, deployed-code binding, complete command-level refinement, and funded testnet validation are outside the current verification coverage. [The compatibility and safety register](docs/PARITY_MATRIX.md) records current coverage.
