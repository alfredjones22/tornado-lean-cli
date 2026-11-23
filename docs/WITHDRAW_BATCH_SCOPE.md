# Native batch withdrawal scope

`Tornado/Cli/WithdrawBatch.lean` implements the read-only `withdraw batch --dry-run` review; `SponsoredWithdraw.lean` connects the explicit `--experimental-send` route. Both select 2–12 same-asset notes, or 1–12 when contract calls are present, and derive the owner through the protected native key boundary. They check the locally predicted SimpleAccount v0.8 address, pinned factory/implementation, EntryPoint, and any deployed account's owner and implementation slot. Dry-run reads protected note data and prints account, receiver, total value and ordered call hashes without making a proof, signature, journal or submission. Live mode keeps note secrets in the separate prover worker.

The parsed call formats are raw `[{"to","value","data"}]` JSON and Safe Transaction Builder v1.0. Values are decimal wei strings. Only ordinary `CALL` operations are allowed. The parser checks nonzero EIP-55 targets, uint256 values, even-length calldata, at most 12 user calls, 16 KiB per call, and 64 KiB total. Calls to the smart account itself are blocked. An external receiver cannot be combined with contract calls. The ordered hash is the native ABI hash of the exact `(address,uint256,bytes)[]` sequence. Native `ImportedAbi` re-encodes `contractMethod` and `contractInputsValues`, checks payable behavior and any supplied calldata, and supports bounded standard integers, addresses, booleans, bytes, strings, tuples and arrays. Nesting is capped at 12, arrays and tuple components at 1,024, and final calldata at 16 KiB. Explicit nonstandard integer widths are rejected. Twenty-eight pinned viem encoding/hash vectors and twenty rejection cases cover this import path.

Supported options: `--notes-file`, `--owner-key-file`, `--receiver`, `--contract-calls`, `--chain`, `--rpc`, `--bundler-url`, `--status-dir`, `--dry-run`. `--simulation-rpc`, `--assets-dir`, and `--yes` are accepted but have no effect in this dry run, as in the pinned TypeScript route. The bundler URL is syntax-checked but not contacted. The RPC is contacted only for smart-account identity reads. The native transport accepts HTTPS or explicit loopback HTTP for local development.

The RPC is still an external chain-truth assumption; code/hash and state checks protect against mismatched responses but do not establish Ethereum consensus. The owner address comes from the protected native public-key boundary, so this dry run does not load the owner key into Lean. The note backup still enters Lean-managed memory and is not zeroized. No key bytes, note, preimage, nullifier, or full contract-call JSON are printed.

Experimental send requires `--experimental-send`, a protected `--owner-key-file`,
and typed `WITHDRAW`; it rejects `--yes`, replacement retries and mixed modes.
The owner key stays inside the native signer. The command shares the key-directory
sender lock with deposits/recovery and exclusively reserves every selected
note's opaque status path before executable exposure. Dummy-only gas estimation
stabilizes the proof-bound fee before real proofs are generated. After slow
proving, selected history/known roots, account identity/nonce and fresh host fee
bounds are checked before the five-minute final review window starts, then
checked again after approval. The ordered operation binds sponsor payouts,
zero-fee remaining notes, owner, recoverable account, receiver and exact tail
calls.

The signed final operation is journaled and marked exposed before
`eth_simulateV1`, because its RPC can relay it. A known failure always blocks.
Default `--simulation-policy required` blocks unavailable simulation;
`best-effort` admits only narrowly classified unavailability after successful
dummy estimation. There is at most one final simulation and bundler send.
Uncertain or partially persisted outcomes retain every candidate/reservation
and the sender lock; there is no automatic replacement. Exact receipt,
EntryPoint event and every selected pool Withdrawal event gate confirmation.
The send adapter waits for twelve observed confirmations before owner-lock
release. Batch status preserves mirror evidence through protected CAS and an
authoritative in-progress marker; partial writes report uncertainty.

The sponsoring note is withdrawn during paymaster validation. A subsequent
execution failure does not imply that note is unspent or that the whole batch
rolled back atomically. Funds may remain in the recoverable account. Reconcile
the original candidate and inspect `smart-account show`/`smart-account recover`;
do not create a replacement merely because the UserOperation failed. Full
success requires all expected events. Standalone status checks observed receipt
inclusion, while the send adapter additionally waits for twelve confirmations.

Focused verification includes `tests/WithdrawBatch.lean`,
`tests/ImportedAbi.lean`, paymaster/network/submission tests, and a real worker
proof on a public unfunded fixture. The tests do not submit funded
transactions. The worker's variable-time/nonzeroizing Lean arithmetic has
no constant-time or secure-erasure guarantee. Finite offline tests and
selected pure theorems do not prove full command parity, end-to-end fund safety,
RPC truth, deployed-code correctness or consensus finality.
