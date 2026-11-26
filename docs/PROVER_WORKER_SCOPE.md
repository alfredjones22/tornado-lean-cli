# Experimental Classic prover worker

The compiled [`tornado_prover_worker`](../Tornado/Cli/ProverWorkerMain.lean) is a separate native Lean process used by experimental live withdrawal commands. Tests use **public, unfunded fixtures** and do not submit a transaction. Its arithmetic is variable-time and it does not guarantee reliable secret erasure. The parent-side [`ProverWorkerClient`](../Tornado/Runtime/ProverWorkerClient.lean) sends a bounded canonical request containing the selected chain, pool, commitment, nullifier hash, Merkle root and path, and the six reviewed public withdrawal inputs. No note preimage, nullifier preimage, secret, mnemonic, or blinding scalar belongs in the request or response. The combination of commitment, nullifier hash, and recipient can link deposit and withdrawal activity; the request is privacy sensitive and must not be logged or kept.

The child authenticates the pinned circuit, proving key, and witness graph before opening the protected note backup. It checks the selected note against the requested chain, pool, commitment and nullifier hash, rejects a zero recipient and fees that consume the note, recomputes the note identifiers and Merkle membership, samples fresh Groth16 blinding, and generates the 256-byte Solidity proof. It emits only the canonical public proof and six signals. Errors are fixed text and do not include parsed note content. Full direct, paymaster, or relayer fee and address policy remains a caller responsibility.

Withdrawal commands default to Ethereum mainnet (`--chain 1`). Sepolia notes require `--chain 11155111` for both `withdraw one` and `withdraw batch`; the command does not infer a network from the backup. Note inspection checks the selected network before proof generation. Parent-side inspection failures show the selected network and fixed guidance about the chain flag, protected file permissions, note selection and rebuilding the worker. They do not echo worker stderr, note contents or secret-dependent failure details. Wrong-chain inspection rejects the backup; it is not a failed Groth16 proof.

Before launching metadata inspection, the parent checks path metadata without opening the note file. Missing paths report the exact resolved filename and explain shell tilde expansion; directories, symlinks, multiple hard links, empty files and oversized files have separate diagnostics. These metadata checks do not replace the worker's protected read, owner/permissions/ACL validation or stability checks. Withdrawal status files are checked only after successful metadata inspection, so removing prior withdrawal journals does not fix a metadata-path failure.

The parent never reads the note. It caps worker output and execution time, rejects noncanonical JSON and changed request hashes or signals, strictly decodes all eight proof words as canonical curve points, verifies the Groth16 equation against the compiled Classic verifying key, and then constructs public pool calldata. [`Accepted`](../Tornado/Runtime/ProverWorkerClient.lean) carries Lean evidence that the accepted proof and calldata are bound to those reviewed public inputs. This is a conditional guarantee about the local acceptance function; it does not authenticate Ethereum state.

The launcher caches each child's first observed exit status while waiting for its output reader. Lean's `tryWait` reaps the process and cannot be polled again after returning a status. The same cache is shared with error cleanup, so an already reaped process is neither waited on again nor signaled using a potentially reused process identifier. Time and output limits remain enforced. `tests/WorkerProcess.lean` forces exit before stdout EOF and covers repeated single/batch inspection, malformed output, nonzero exit and timeout without reading user notes or making network requests.

The focused unfunded fixture runs through the real child process and checks the returned proof and calldata against the reviewed public inputs. Fresh blinding means its proof bytes need not equal a deterministic SDK fixture. A separate client test accepts a pinned SDK public proof and rejects changed hashes or signals and invalid proof encodings. The wire test rejects malformed records. `node scripts/verify.mjs` includes these checks in the full validation gate.

The read-only `--inspect` mode returns bounded, canonical public note metadata
and the opaque status filename. `ProverWorkerClient.inspectPrototype` lets a
caller select public identity without reading the secret backup in
the parent. Metadata is checked against the pinned catalog. Its association
of commitment and nullifier hash remains privacy sensitive. It does not
authenticate the worker executable or Ethereum state.

The worker also supports direct note-derived signer inspection and signing.
Canonical request/response records bind the selected public note identity,
expected sender and exact operation hash; the parent does not receive the
derived private key. Batch owner keys instead use the protected native
libsecp256k1 key-file boundary. The child signer is still variable-time Lean
cryptography, without a constant-time or complete-erasure guarantee.

## Restricted program and release proofs

The actual dispatcher constructs
[`WorkerProgram.Program`](../Tornado/Runtime/WorkerProgram.lean), whose effects
are configured note/request reads, four fixed asset slots and explicit
32-byte entropy draws. Request reads require sign/prove mode; asset and
entropy access require prove mode. The native interpreter attempts core-dump
suppression before input access and stops if it fails. Public request reads
are capped at 4,096 bytes; compressed circuit/key and witness-graph slots are
capped at 4/32/16 MiB respectively; the public witness certificate has a
2 MiB compressed cap and a 16 MiB decompressed cap. The private note uses the protected reader.
There is no network, file-write, arbitrary-path or logging operation in the
program, and no unrestricted prover IO callback.

[`WorkerDisclosure`](../Tornado/Spec/WorkerDisclosure.lean) kernel-checks those
capability restrictions and the terminal gate: one canonical typed response
line with no embedded CR/LF or one fixed failure diagnostic. Proof/signature
release rechecks request binding. Injected read/entropy/protection failures
and actual oversized input paths have focused tests; the real-child public
fixture exercises the refactored prover.

The capability statements alone do not rule out secrets encoded in an
allowed cryptographic output. The separate
[`original_worker_output_privacy`](../app-proofs/TornadoProofs/WorkerPrefix.lean)
now proves a conditional statistical statement about the exact proof
program's stdout, stderr and exit status. Under its explicit source and
honest-setup hypotheses, independently admitted notes with the same public
setup and signals differ on every output event by at most `2^-251`, including
all later proof failures and sampler exhaustion. This does not cover arbitrary
note-parser failures, signing/metadata contents, physical partial output,
timing, resources, crashes or memory remnants.

The interpreter and installed executable remain trusted. The configured
history RPC can associate selected deposit receipt and nullifier-spent queries;
this worker boundary does not hide that parent-side linkage.

## Experimental and production limits

- The child handles spendable note bytes, witness values, FFT/MSM intermediates, blinding scalars and note-derived signer secrets in Lean-managed memory. Its arithmetic is variable time and these copies are not reliably erased. A separate process shortens their lifetime but is **not** an audited constant-time or zeroizing prover boundary. `--broadcast` does not change these limitations.
- The caller must independently establish that the requested root and leaf correspond to the selected pool's accepted chain state, that the note is unspent, and that the chain, recipient, route, fee, and deployed code match what the user reviewed. A valid proof for an arbitrary supplied root does not establish those facts. RPC and Saga data are external claims.
- The raw worker enforces field bounds and proof binding; its caller must enforce route policy. Connected `PaymasterPrepare` and `SponsoredWithdrawal` modules check paymaster quotes, payouts and ordered calls. `RelayerSend` checks registered relayers and the 20% fee cap and exposes a one-POST executor. `SponsoredWithdraw` and `RelayerWithdraw` join public metadata, history, typed review, protected per-note reservations and the worker without reading note bytes in the parent.
- The launcher accepts an absolute worker executable path and gives that process the protected note path. The runnable CLI selects the sibling `tornado_prover_worker`; its installation is trusted, not cryptographically authenticated. A substituted executable could read and disclose the note. The note-file path also appears in child process arguments.
- The worker executable, note-file path, asset directory, OS process isolation, filesystem, entropy source, compiler, Lean runtime, and verifier implementation remain trusted. A fatal runtime crash can bypass sanitized error handling; process termination is not a proof of complete secret erasure.
- The worker itself does not submit transactions or proofs to remote providers. Parent adapters own protected journals, exposure marking, final signed simulation, one-shot bundler/relayer submission and status reconciliation. Their injected fault tests do not constitute an end-to-end theorem about real filesystem/network effects.

Secret-safe witness/prover computation and complete physical IO refinement
are outside the current verification coverage. Sponsored withdrawals use
a proved command machine, conditional on its callback contracts; this does
not prove all CLI routes or durable OS effects. Protecting only the
final curve arithmetic would leave note, witness and intermediate copies in
Lean memory; the complete secret-bearing computation is relevant to this limit.
