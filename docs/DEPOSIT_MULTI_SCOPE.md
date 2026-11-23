# Multi-note deposits

[`DepositMulti.lean`](../Tornado/Cli/DepositMulti.lean) implements a native,
read-only `deposit send --dry-run` planner for 1–100 notes from a protected
backup. It derives each public commitment in Lean, then discards note
preimages from the planner's `Item` type. The output includes only sender,
amounts, pool targets, public calldata, approvals, and route information.

The selected RPC supplies chain ID, sender code, pending ETH balance, token
balance, each pool's `denomination()`, and each pool's token allowance. The
planner rejects wrong-chain or unsupported pools, duplicate commitments,
mixed assets, missing/duplicate pool readings, denomination mismatches, and
insufficient deposit balance. It chooses sequential EIP-1559 calls when
`--sequential` is requested or the sender already has code. An undelegated EOA
with multiple calls previews Simple7702 batches; a single approval-free note
uses one ordinary transaction. Token approvals are exact for each pool; a
nonzero insufficient allowance inserts a reset first. Batch limits match the
pinned CLI: 12 ETH notes or 5 token notes, with a singleton final chunk
avoided. Later preview batches show deposit calls only; the send engines
re-read allowances and re-plan before each batch.

The compiled `deposit_multi_test` passed sequential/7702 selection, forced
sequential mode, single-note routing, wrong-chain/denomination/balance and
duplicate rejection, six-token-note 4+2 chunking, exact reset/approval
amounts, and private backup reduction to two public commitments.

`deposit send --experimental-send --journal <new-path>` connects the separate
native send engines. `DepositMultiSend.lean` executes sequential EIP-1559
transactions through `ProtectedTxSender.lean`; `DepositBatch7702.lean` handles
Simple7702 batches and automatic selection. Both use the protected native
signer, the invoice route's sender lock and permanent commitment claims,
exclusive new journals, and protected compare-and-replace updates. They
recheck chain, sender, nonce and exact calls after typed approval, record
the signed hash before exposure, and stop after any uncertain send. Receipts
must match the exact indexed transaction and every selected Deposit event.
Live adapters wait for twelve block confirmations before continuing.

Simple7702 also checks the pinned implementation bytecode and EntryPoint,
requires an undelegated EOA initially, asks for typed `DELEGATE` consent, and
persists the exact signed authorization before bundler estimation can see it.
Delegation persists even if later deposits are cancelled. It records the
reviewed UserOperation before its single submission attempt. Later batches
require the exact session delegation and fresh account nonces. `--sequential`
uses ordinary transactions instead.

The injected tests cover two batches, viem encoding/signature vectors,
changed keys/nonces/plans, failed journal writes, excessive fee quotes,
ambiguous replies, mismatched transaction data, missing events, and failed
confirmation waits. No test used funds. These routes remain experimental;
their C/OS/HTTP effects and end-to-end fund safety are not formally proved.
RPC values remain claims from the configured endpoint, not chain consensus.
