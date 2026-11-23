# Native one-note withdrawal scope

`withdraw one` dispatches local/read-only modes through `WithdrawOne.lean` and
explicit experimental sends through `SponsoredWithdraw.lean` or
`RelayerWithdraw.lean`.

- `--dry-run` reviews the selected protected note, EIP-55 recipient, route,
  pool/value, bundler hostname and opaque HMAC-SHA256 status filename. It makes
  no network call and creates no status file.
- `--preflight` adds bounded selected-pool history, exact-block receipt, leaf,
  root and spent checks. It creates no proof or signature. History assets and
  protected caches are supported. The spent query discloses the nullifier hash
  to the configured RPC.
- `--experimental-send --route 4337|relayer` prepares and submits an exact
  reviewed withdrawal. It requires typed `WITHDRAW`; `--yes` and
  `--retry-rejected` are unavailable for live sends. Mixing read-only and send
  modes is rejected. Classic relayers support original Tornado pools only.

Common inputs are `--note-file`, `--recipient`, optional `--note-index`,
`--chain`, `--rpc`, `--status-dir`, `--assets-dir` and `--history-cache-dir`.
Sponsored mode additionally accepts bundler/simulation settings. The executable
locates its sibling native Lean prover worker and bundled proving assets;
`--proving-assets-root` can select the authenticated asset root.

The live parent reads only bounded public metadata, history and proof results;
the worker opens the protected note, generates the proof and, for direct 4337,
produces note-derived signatures. Proofs are checked against the compiled
Classic key and exact reviewed signals. The worker remains variable-time and
does not reliably erase Lean-managed secrets. Experimental live commands
do not provide constant-time or secure-erasure guarantees.
The installed worker executable is also trusted rather than authenticated.

Sponsored estimation uses only fixed dummy proofs, signatures and
authorizations, with bounded fees/gas and explicit failure classification.
After real proving finishes, history/known roots, unused sender state and fresh
host fee bounds are checked before starting the final review window, then
checked again after approval. The exact signed executable operation and final
EIP-7702 authorization are reserved and marked exposed in a protected journal
before the single bundler send. Direct one-note mode does not run the batch's
final signed execution simulation. An uncertain send retains the candidate
and blocks replacement; a failed UserOperation is not permission to retry.

Classic relayer mode binds the selected pool, recipient, registered reward
account, positive bounded fee and zero refund to the verified proof. It
revalidates quote/registration/history after approval, exclusively creates its
protected claim before one proof POST, and never repeats an uncertain POST.
Missing job IDs or a relayer's status alone cannot confirm a withdrawal.

Both routes use the same opaque per-note status filename within the selected
status directory, preventing a route switch there from bypassing an existing
attempt. Claim filenames are keyed by the note's secret nullifier preimage;
they disclose no raw note. Candidate/reservation evidence survives unknown or
partially persisted outcomes. Do not delete it or change status directories to
force a replacement. Exact chain receipt/pool events gate status confirmation;
4337 also requires exact EntryPoint evidence. Sponsored send waits for twelve
observed confirmations, while relayer status currently reports exact observed
inclusion without that depth wait. Neither proves consensus finality.

`tests/WithdrawOne.lean` covers read-only review. Worker/proof, session,
paymaster, network, submission, journal and relayer tests use public unfunded
fixtures and injected faults. The tests do not submit funded transactions.
These are finite tests plus selected policy theorems, not
full TypeScript parity or an end-to-end correctness proof. Consistent false
RPC state, contract/crypto assumptions and native OS boundaries remain outside
the guarantee.
