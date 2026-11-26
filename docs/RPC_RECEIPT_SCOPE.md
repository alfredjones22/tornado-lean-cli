# Native RPC receipt reconciliation boundary

[`RpcReceipt.lean`](../Tornado/Protocol/RpcReceipt.lean) parses the
`eth_getTransactionReceipt` and `eth_getUserOperationReceipt` JSON-RPC result
shapes used by the native command adapters. It shares the native JSON-RPC 2.0
envelope and quantity parser with `Tornado/Runtime/JsonRpc.lean`.

The parser requires the requested transaction hash, block hash and number,
transaction index, status, origin, destination, and logs. Every log must carry
the same transaction and block identifiers as its parent receipt; log indexes
must increase, `removed` must not be true, addresses must be 20 bytes, topics
32 bytes, and status exactly `0x0` or `0x1`. The bundler result is only a hint:
it must bind the reviewed UserOperation hash, EntryPoint, sender, paymaster and
nonce, but confirmation still requires the separate chain receipt and native
EntryPoint/pool event checks. A null result means no receipt yet.

The [fixture](../fixtures/rpc-receipt-vectors.json) combines the pinned viem
2.55.19 event vectors with synthetic JSON-RPC metadata and is accepted by
viem's `formatTransactionReceipt` and `formatUserOperationReceipt`. The
[test](../tests/RpcReceipt.lean) passes 16 exact checks and 21 rejection checks,
covering direct and batch withdrawals, sequential and batch deposits, relayer
withdrawals, failed UserOperations, malformed metadata, and contradictory
bundler hints.

Three kernel-checked theorems prove that the pure direct-withdrawal,
batch-withdrawal, and batch-deposit gates cannot report confirmation without
the expected transaction hash, EntryPoint destination, and their respective
strict native event outcomes. Theorems import the exact gate functions; they
depend only on Lean's standard axioms. They do **not** prove the JSON came from
an authentic chain, that `eth_chainId` matched the selected network, that the
block is canonical or finalized, or that an arbitrary caller-supplied `Receipt`
was produced by this parser. Native deposit, withdrawal, recovery, history and
status paths use this parser and its event gates through their runtime adapters.

Input bounds of 4,096 logs per receipt, four topics per EVM log, and one MiB
per log data field limit parser allocations. Effectful callers separately check
the configured chain, request ID and recorded transaction hash and retain
uncertain signed candidates. These parser theorems do not establish those
callers' complete execution traces or authenticate reorg/finality claims.
