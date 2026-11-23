# Native smart-account recovery

`smart-account recover` supports read-only review and an explicitly experimental
owner-paid send. [`SmartAccountRecover.lean`](../Tornado/Cli/SmartAccountRecover.lean)
provides the review; [`RecoverySend.lean`](../Tornado/Cli/RecoverySend.lean)
connects protected signing, journaling and exact confirmation.

```text
smart-account recover --owner <EOA address> --dry-run
smart-account recover --owner-key-file <path> --dry-run
smart-account recover --owner-key-file <path> --experimental-send --journal <new-path>
  [--owner <expected EOA>] [--receiver <address>] [--chain <1|11155111>] [--rpc <URL>]
```

The receiver defaults to the owner and the chain defaults to mainnet. Live mode
requires typed `RECOVER` approval and rejects `--yes`. Protected owner-address
derivation and signing occur inside the native libsecp256k1 boundary; key bytes
do not enter Lean. Dry-run creates no journal, signature or submission.

The review checks the RPC chain, captures one block, and uses that block for
code, storage, balances and calls. It checks pinned factory/implementation
hashes, the locally predicted account address and factory response, owner code
type, account owner, EntryPoint, implementation slot and nonce. Supported
ETH/ERC-20 sweeps and optional EntryPoint-deposit withdrawal are encoded in
exact order. Undeployed/empty accounts, self-recipients and mismatched identity
fail closed. Unsupported assets require separate owner-authorized actions.

After approval the adapter reloads the protected key identity and rechecks the
account, balances and exact recovery calls. The candidate must be a zero-value
type-2 owner transaction to that account with exactly the reviewed calldata,
empty access list, selected chain and bounded nonce/gas/fees. A new protected
journal records signed bytes' hash before RPC broadcast. The same key-directory
sender lock is shared with deposit and smart-account withdrawal senders. Errors
after signing starts retain it; there is no automatic replacement or resend.

An exact indexed transaction and receipt must agree on hash, sender,
destination, calldata, type, zero value, chain and block inclusion. The send
adapter waits for twelve observed confirmations before releasing the lock;
standalone `smart-account status` reconciles observed inclusion without proving
finality. Journal updates use protected byte-for-byte compare-and-replace.
Unknown outcomes preserve evidence and require reconciliation.

Focused offline tests: `tests/SmartAccountRecover.lean`,
`tests/RecoverySend.lean`, and `tests/SmartAccountStatus.lean`. They exercise
candidate binding, changed review, wrong key, journal-before-send failures,
ambiguous sends, stale CAS, exact receipt checks and lock retention. They make
no real or funded transaction. These tests and selected pure theorems do not
prove the complete runnable effect trace. RPC truth, deployed contracts,
cryptography, native signing, OS memory/filesystem behavior and actual storage
durability remain assumptions.
