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
- `--broadcast --route 4337|relayer` prepares and submits an exact
  reviewed withdrawal. By default it requires typed `WITHDRAW`; explicit
  `--non-interactive` skips that confirmation while still printing the review.
  Validation, fee bounds, revalidation, protected claims/journals and
  uncertain-outcome handling remain in force. `--yes` and
  `--retry-rejected` are unavailable for live sends. Mixing read-only and send
  modes is rejected. Classic relayers support original Tornado pools only.

Common inputs are `--note-file`, `--recipient`, optional `--note-index`,
`--chain`, `--rpc`, `--status-dir`, `--assets-dir`, `--history-cache-dir` and
`--non-interactive`. Run `--dry-run` first; `--non-interactive` alone does not
enable broadcasting. One-note withdrawals use the protected note backup and
need no account key file.
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
The direct verification baseline is 50,000 gas. Returned measurements receive
20% headroom; omitted optional paymaster verification or post-operation fields
retain their current floors without repeatedly buffering them. Explicit zero
measurements also retain those floors, while malformed supplied fields are
rejected. Gas-bound errors identify the bounded numeric field, value and
configured ceiling without reflecting provider error text.
If the host base fee is below 1,000,000 wei/gas, the initial maximum fee gets
up to 1,000,000 wei/gas of headroom within the unchanged host-reference and
absolute caps. Both original and padded quotes pass the existing checks;
priority is unchanged, and this initial bid is used to compute the note fee
bound by the proof. After proving, before final review or the first signature,
direct sponsored withdrawals fetch a fresh validated bid and may lower the
maximum fee and priority. Neither price can increase, and all five gas limits,
proofs, public inputs, note fees and payouts remain unchanged. If a valid current
bid cannot fit the prepared budget, preparation stops before signing.

The note fee is the amount withdrawn to the paymaster, distinct from the
operation's maximum network gas cost. The original note fee can therefore
exceed the cost implied by the lowered bid. The paymaster may refund unused
fees to the reviewed recipient; a refund is not guaranteed. The final review
shows the unchanged note fee and payout alongside the final network cost and
operation hash. After final review there is no bid refresh: strict revalidation
still rejects expired or excessive prices, with bounded numeric fee details.
Unavailable or malformed gas-reference data has separate RPC guidance.
Only gas-price refresh reads can retry the native binding's exact transport
unavailability result: at most two shared backoffs of 500 and 1,000 ms across
fee-history and fallback reads. This does not retry writes, signed simulation
or submission.
The default `--simulation-policy required` requires a successful estimate,
except for the exact known zero-execution estimator incompatibility below.
Some bundlers replace an explicitly zero execution-gas limit with a search
ceiling, causing `AA33` with `CallGasLimitNonZero(uint256)`. The native adapter
recognizes only the exact nonzero custom error for empty calldata and a
canonical zero execution limit, with the observed paymaster rejection code
and no extra error data. For direct single-note withdrawals, this known case
automatically uses the existing bounded conservative fallback, including under
the default policy. No extra flag is needed. Recognized transport/internal
outages still require explicit `--simulation-policy best-effort`.
Execution gas stays zero, the fee is recalculated and bounded before proving,
and the final review identifies the automatic known-incompatibility fallback. Batch
withdrawals and execution-bearing operations cannot use this exception;
other validation failures remain rejected. Remote messages and request bodies
are not printed.
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
4337 also requires exact EntryPoint evidence. Sponsored send and relayer status require exact observed inclusion. Neither proves consensus finality.

`tests/WithdrawOne.lean` covers read-only review. Worker/proof, session,
paymaster, network, submission, journal and relayer tests use public unfunded
fixtures and injected faults. The tests do not submit funded transactions.
These are finite tests plus selected policy theorems, not
complete command correctness or an end-to-end correctness proof. Consistent false
RPC state, contract/crypto assumptions and native OS boundaries remain outside
the guarantee.
