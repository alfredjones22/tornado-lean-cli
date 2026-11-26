# Internal one-note proof-to-call builder

[`WithdrawProof.lean`](../Tornado/Cli/WithdrawProof.lean) composes the native
one-note withdrawal primitives. The prover worker uses its authenticated asset
loader; runnable commands use the separate worker/session route rather than
the parent-side reference wrapper described here. That wrapper selects exactly
one note from a protected backup, checks
the selected pool through the pinned catalog, bootstraps and syncs its history
through the native Saga/RPC validator, and rechecks the root, leaf count, and
`isSpent(bytes32)` claim at the captured head. It authenticates the bundled
compressed circuit, proving key, and extracted witness graph. It builds the
selected note's 20-level MiMC path, samples two nonzero canonical Fr scalars
from separate kernel CSPRNG reads, runs the full native R1CS/Groth16 prover and
compiled Classic verifier, then ABI-encodes `withdraw(bytes,bytes32,bytes32,
address,address,uint256,uint256)`.

The route shapes are direct pool call (`relayer=0`, `fee=0`), pinned SDK
paymaster address with a caller-provided fee below the note amount, and Classic
relayer reward account with an original-pool restriction and at most 20% note
fee. Neither relayer registration nor an external fee quote is checked here.
The returned `Call`
contains only public pool, recipient, relayer, fee, root, nullifier hash, proof
bytes, calldata, and history head. It contains no note preimage or Merkle
witness. This module constructs a pool call, not an ERC-4337 UserOperation
or relayer job; submission adapters are separate.

The public deterministic fixture test uses a synthetic one-deposit pool state
and fixed `r=1,s=2` solely to compare its 256 proof bytes against the pinned
SDK oracle. It also checks the exact Solidity ABI layout and rejects a spent
note, changed root, wrong direct fee, and unsupported relayer route. Fixed
blinding values must never be used for a funded note. The live internal entry
uses fresh rejection-sampled scalars instead.

## Security and completeness boundary

- Lean's big-integer, elliptic-curve, FFT, and pairing code are variable-time
  and do not zeroize secrets. The native prover has no side-channel review.
  Runnable experimental commands use the isolated worker/session path instead
  of importing note secrets into this parent-side reference builder. The worker
  still has the same arithmetic/erasure limitations and no production
  secret-safety guarantee.
- `HistorySync.Result` is a plain data structure for the deterministic test.
  The live internal wrapper obtains it from native sync and exact-block RPC
  checks. RPC responses, Saga coverage, canonical chain state, finality, and
  deployed pool/paymaster code are not cryptographically proved here.
- The exact-block `isSpent` call discloses the selected note's public nullifier
  hash to the configured RPC. A reorg after the captured head can change
  spendability. A pool with more than the history engine's fresh-scan budget
  cannot be prepared without an authenticated cached state.
- This reference builder does not create a fee quote, recovery journal, signed
  UserOperation, relayer submission, broadcast, or receipt confirmation.
  Separate command adapters implement those effects. The ABI data alone does
  not authorize a safe spend.
