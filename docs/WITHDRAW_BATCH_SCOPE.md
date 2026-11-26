# Native batch withdrawal scope

`Tornado/Cli/WithdrawBatch.lean` implements the read-only `withdraw batch --dry-run` review; `SponsoredWithdraw.lean` connects the explicit `--broadcast` route. Both select 2–12 same-asset notes, or 1–12 when contract calls are present, and derive the owner through the protected native key boundary. They check the locally predicted SimpleAccount v0.8 address, pinned factory/implementation, EntryPoint, and any deployed account's owner and implementation slot. Dry-run reads protected note data and prints account, receiver, total value and ordered call hashes without making a proof, signature, journal or submission. Live mode keeps note secrets in the separate prover worker.

The parsed call formats are raw `[{"to","value","data"}]` JSON and Safe Transaction Builder v1.0. Values are decimal wei strings. Only ordinary `CALL` operations are allowed. The parser checks nonzero EIP-55 targets, uint256 values, even-length calldata, at most 12 user calls, 16 KiB per call, and 64 KiB total. Calls to the smart account itself are blocked. An external receiver cannot be combined with contract calls. The ordered hash is the native ABI hash of the exact `(address,uint256,bytes)[]` sequence. Native `ImportedAbi` re-encodes `contractMethod` and `contractInputsValues`, checks payable behavior and any supplied calldata, and supports bounded standard integers, addresses, booleans, bytes, strings, tuples and arrays. Nesting is capped at 12, arrays and tuple components at 1,024, and final calldata at 16 KiB. Explicit nonstandard integer widths are rejected. Twenty-eight pinned viem encoding/hash vectors and twenty rejection cases cover this import path.

Supported options: `--notes-file` (alias `--note-file`), `--owner-key-file`, `--receiver` (alias `--recipient`), `--contract-calls`, `--chain`, `--rpc`, `--bundler-url`, `--status-dir`, `--dry-run`, `--non-interactive`. `--simulation-rpc`, `--assets-dir`, and `--yes` are accepted but have no effect in this dry run. Native `--history-cache-dir` and `--proving-assets-root` are also accepted in separated or equals forms so the live preparation paths can stay on the preview command. Their values must be supplied, but dry-run does not read those paths, validate cache permissions, synchronize history or load proving assets. The bundler URL is syntax-checked but not contacted. The RPC is contacted only for smart-account identity reads. The native transport accepts HTTPS or explicit loopback HTTP for local development.

The RPC is still an external chain-truth assumption; code/hash and state checks protect against mismatched responses but do not establish Ethereum consensus. The owner address comes from the protected native public-key boundary, so this dry run does not load the owner key into Lean. The note backup still enters Lean-managed memory and is not zeroized. No key bytes, note, preimage, nullifier, or full contract-call JSON are printed.

Run `--dry-run` first. Experimental send requires `--broadcast` and, by default,
typed `WITHDRAW`. Explicit `--non-interactive` skips that confirmation while
still printing the review and retaining validation, fee bounds, revalidation,
protected journals, reservations and uncertain-outcome handling. It requires
a protected `--owner-key-file` in both dry-run and broadcast modes and does not
enable sending by itself. Live sends reject `--yes`, replacement retries and
mixed modes. Without `--non-interactive`, the optional `--owner-key-file`
selects a protected file; omitting it opens a hidden terminal prompt in both
dry-run and broadcast modes. The owner key stays inside the native signer.
Interactive mode anchors reservations in the home directory. The command shares the signing-directory
sender lock with deposits/recovery and exclusively reserves every selected
note's opaque status path before executable exposure. Dummy-only gas estimation
stabilizes the proof-bound fee before real proofs are generated. After slow
proving, selected history/known roots, account identity/nonce and fresh host fee
bounds are checked before the five-minute final review window starts, then
checked again after approval. The ordered operation binds sponsor payouts,
zero-fee remaining notes, owner, recoverable account, receiver and exact tail
calls.

For an undeployed smart account, live batch preparation starts with 1,000,000
verification gas and uses a route-specific ceiling of 2,000,000. A deployed
account starts at 50,000, as does direct one-note preparation. The general
bundler verification ceiling remains 1,000,000; the larger ceiling is supplied
only for the account-deployment batch route and carried through final review.
Returned gas measurements receive 20% headroom and must stabilize within the
local limits. An omitted optional paymaster verification or post-operation
field retains its current floor without buffering that floor again. An
explicit zero measurement also retains the floor. Malformed supplied fields
are rejected. Gas-bound errors name the specific bounded numeric field, value
and ceiling, without printing provider error text or unknown response fields.

When the host base fee is below 1,000,000 wei/gas, preparation adds up to
1,000,000 wei/gas to the initial maximum fee. The original quote must pass the
existing checks first; the padded quote remains within the same host-reference
and absolute price caps and is checked again. Priority is unchanged. This
initial bid is used to compute the sponsoring note fee bound by the proof.
After proving, before final review or the first signature, a batch without
custom contract calls fetches a fresh validated bid and may lower its maximum
fee and priority. Neither price can increase. All five gas limits, proofs,
public inputs, note fees, recipients and forwarding amounts remain unchanged.
The prepared quote is retained; the checked final bid is passed separately
into the final review and unsigned operation. If a valid current bid cannot
fit the prepared budget, preparation stops before signing.

Custom contract calls retain the original bid because their behavior can
depend on `GASPRICE`; expired or excessive prices stop preparation. After
final review, all routes use strict revalidation without changing the bid,
fee or proof. Price failures include bounded numeric details, while an
unavailable or malformed gas-reference read has separate RPC guidance.

The sponsoring note fee is the amount withdrawn to the paymaster, distinct
from the operation's maximum network gas cost. This original fee can exceed
the cost implied by a lowered bid. Any unused-fee refund is conditional and
goes to the recoverable smart account, including when the withdrawal proceeds
are forwarded to an external receiver; it is not a guaranteed extra payout.
The final review continues to show the original note fee and net withdrawal
alongside the final network cost and operation hash.

Gas-price refresh reads alone may retry the native binding's exact transport
unavailability result, with at most two shared backoffs of 500 and 1,000 ms
across the fee-history and fallback reads. Other rejections do not acquire
this retry path. These read retries do not retry a write, signed simulation
or bundler send.

The signed final operation is journaled and marked exposed before
`eth_simulateV1`, because its RPC can relay it. A known failure always blocks.
Default `--simulation-policy required` blocks unavailable simulation;
`best-effort` admits only narrowly classified unavailability after successful
dummy estimation. There is at most one final simulation and bundler send.
The automatic workaround for a zero-execution `CallGasLimitNonZero` estimator
error applies only to validation-only direct withdrawals. A batch contains
execution calls and must still obtain a successful dummy gas estimate under
either policy; a matching-looking error cannot bypass its validation.
Uncertain or partially persisted outcomes retain every candidate/reservation
and the sender lock; there is no automatic replacement. Exact receipt,
EntryPoint event and every selected pool Withdrawal event gate confirmation.
The send adapter rechecks one observed inclusion before owner-lock
release. Batch status preserves mirror evidence through protected CAS and an
authoritative in-progress marker; partial writes report uncertainty.

The sponsoring note is withdrawn during paymaster validation. A subsequent
execution failure does not imply that note is unspent or that the whole batch
rolled back atomically. Funds may remain in the recoverable account. Reconcile
the original candidate and inspect `smart-account show`/`smart-account recover`;
do not create a replacement merely because the UserOperation failed. Full
success requires all expected events. Standalone status and the send adapter both check observed receipt
inclusion.

Focused verification includes `tests/WithdrawBatch.lean`,
`tests/ImportedAbi.lean`, paymaster/network/submission tests, and a real worker
proof on a public unfunded fixture. The tests do not submit funded
transactions. The worker's variable-time/nonzeroizing Lean arithmetic has
no constant-time or secure-erasure guarantee. Finite offline tests and
selected pure theorems do not prove complete command correctness, end-to-end fund safety,
RPC truth, deployed-code correctness or consensus finality.
