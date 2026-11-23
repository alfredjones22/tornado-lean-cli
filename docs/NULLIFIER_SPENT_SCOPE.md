# Read-only nullifier-spent check

[`Tornado/Cli/NullifierSpent.lean`](../Tornado/Cli/NullifierSpent.lean) exposes
`checkAt` for a selected chain, pinned catalog pool, 32-byte nullifier hash,
block number, and HTTPS RPC. It sends only `eth_chainId`, `eth_blockNumber`,
and an exact-block `eth_call` of `isSpent(bytes32)` to that pool. The call data
uses the Solidity selector `0xe5285dcc` and the selected nullifier hash. The
response must be exactly one canonical ABI bool word (`0` or `1`); malformed
data and RPC failures raise an error rather than becoming `false`.

`checkWith` accepts an injected RPC reader for offline tests. Selection
validation happens before any network request: the pool must be a complete row
in the pinned chain catalog, the nullifier must be exactly 32 bytes, and the
block number must fit in `uint256`. The RPC chain must match and its head must
be at or beyond the selected block. `checkAt` uses the native authenticated
HTTPS transport, including explicit loopback HTTP for local nodes. This is a
reusable checker rather than a standalone command; history and experimental
withdrawal sessions perform their own exact-block spent queries.

**Privacy:** the configured RPC receives the nullifier hash before a spend.
It can retain the query and link it to a later public withdrawal. This privacy
association applies even when the returned value is `false`. The native
transport permits explicit loopback HTTP endpoints for local nodes.

The returned bool is an observation from the configured RPC at a numbered
block, not an Ethereum state proof. Chain identity, canonical history,
provider honesty, and finality are external assumptions. A numbered block
can be replaced by a reorg; callers need a block-hash/finality policy before
using this check to authorize a funded action. A `false` result is not proof
that no competing pending spend exists.

Two Lean theorems establish that an accepted selection binds the pool to the
selected catalog chain and that an accepted `true` RPC word has the exact
canonical encoding. They do not prove RPC honesty or the Solidity pool's
implementation. Run the offline fixture with
`lake env lean --run tests/NullifierSpent.lean`.
