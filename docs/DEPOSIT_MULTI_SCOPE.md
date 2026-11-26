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
`--sequential` is requested. A single note also defaults to ordinary
transactions, even with an existing compatible delegation or required token
approvals. ETH needs one transaction; tokens can need reset/approval transactions
before their deposit. Only `--delegated` selects a UserOperation for one note.
For multiple notes, a sender with the exact 23-byte designator for the pinned
Simple7702 implementation uses batches automatically without a new authorization.
A sender with other code uses the sequential route by default. An undelegated
EOA with multiple notes previews Simple7702 batches.
`--delegated` explicitly selects batches for an undelegated EOA
or a sender with a different valid 7702 designator; it rejects ordinary
contract code and conflicts with `--sequential`. Token approvals are exact for
each pool; a nonzero insufficient allowance inserts a reset first. Batch limits match the
pinned CLI: 12 ETH notes or 5 token notes, with a singleton final chunk
avoided. Later preview batches show deposit calls only; the send engines
re-read allowances and re-plan before each batch.

The compiled `deposit_multi_test` covers sequential/7702 selection, compatible
delegation reuse, forced replacement, single-note routing, wrong chain,
denomination, balance, and duplicate rejection, six-token-note 4+2 chunking, exact reset/approval
amounts, and private backup reduction to two public commitments.

`deposit send --broadcast [--journal <new-path>]` connects the separate
native send engines. `DepositMultiSend.lean` executes sequential EIP-1559
transactions through `ProtectedTxSender.lean`; `DepositBatch7702.lean` handles
Simple7702 batches and automatic selection. Both use the protected native
signer, the invoice route's sender lock and permanent commitment claims,
exclusive new journals, and protected compare-and-replace updates. They
recheck chain, sender, nonce and exact calls after approval, record
the signed hash before exposure, and stop after any uncertain send. Sequential
sends check the indexed transaction against the signed call and receipt;
Simple7702 batches bind the receipt transaction hash, EntryPoint event, and
every selected Deposit event. Both recheck the receipt and containing block
for one validated inclusion, with no further block-depth wait. A later reorg
can still reverse the deposit; this observation is not a finality proof.

Run `--dry-run` first, then choose `--broadcast` separately. Typed `SEND`
confirmation is the default for each transaction or batch. Explicit
`--non-interactive` skips those prompts and any `DELEGATE` confirmation below,
while still printing the reviews and retaining validation, gas/fee bounds,
revalidation, journals, reservations and uncertain-outcome stops. It requires
a protected `--key-file`, including for dry-run and `--resume`; the flag does
not enable broadcasting by itself. `--yes` remains unavailable.

For new sends, `--journal` is optional. Omission selects a visible
`tornado-deposit-<chainId>-<32 hex characters>.json` file in the current directory,
using 128 bits of OS randomness for the name. The selected path is printed.
The adapter still creates it exclusively with private permissions before any
signed transaction is exposed; existing files are never overwritten.
Dry-run creates no journal. `--resume` always requires the original explicit
`--journal` path and never selects a new file or guesses an existing attempt.

Sequential deposits allow up to two million gas including 20% estimation
headroom. The quoted maximum gas cost remains capped at 0.02 ETH per
transaction. ETH deposits above 0.01 ETH also retain the 10% value cap;
deposits at or below 0.01 ETH use only the absolute cap. Custom stricter
bounds are preserved. Failures retain the original diagnostic together with
the journal and sender-lock warning.

Simple7702 also checks the pinned implementation bytecode and EntryPoint. An
empty sender code or explicitly replaced foreign 7702 designator requires
`DELEGATE` consent by default; `--non-interactive` explicitly authorizes skipping
that prompt too. The exact signed authorization becomes durable before
bundler estimation can see it. A sender already carrying the pinned designator
uses its existing delegation without a new authorization, EOA nonce bump, or
factory marker. The engine checks the initial sender code and owner nonce,
then the expected designator at each batch boundary and after approval.
Delegation persists even if later deposits are cancelled. It records the
reviewed UserOperation before its single submission attempt. Later batches
require the exact delegation and fresh account nonces. `--sequential` uses
ordinary transactions instead.

The batch route permits up to 15 million call gas and 16 million total
UserOperation gas. It still caps the quoted maximum network cost at 0.05 ETH.
An ETH batch composed entirely of notes at or below 0.01 ETH is exempt from
the additional 10% batch-value cap, even when their total exceeds 0.01 ETH;
batches containing a larger ETH note retain that cap. The twelve-note
injected case exercises a 13,879,390 call-gas estimate; higher per-call or
combined gas estimates stop before UserOperation signing. These local bounds
do not guarantee that a bundler will accept a twelve-note operation.

Self-funded Simple7702 operations can leave unused gas prefund as an ETH
credit inside EntryPoint under the sender EOA's address. EntryPoint reuses
that credit for future operations; it does not automatically transfer it back
to the EOA's ordinary ETH balance. The live balance guard requires the exact
ETH deposit value plus `max(0, maximumGasCost - EntryPointCredit)` in the EOA;
credit never funds the deposit principal or an ordinary sequential transaction.
The credit is a separate public input to the certified batch planner and is
read again with the wallet balance after approval, before signing. Delegation
uses the bundler-included EIP-7702 authorization rather than a separate EOA
setup transaction. After confirmation, the command reports remaining gas
credit; an unavailable informational read does not undo or fail confirmation.
This is separate from the derived
withdrawal smart account and its recovery command. The EOA owner can withdraw
its credit with an ordinary zero-value transaction to the pinned EntryPoint's
`withdrawTo(owner, amount)` method, paying that transaction's gas from the EOA.
The deposit command does not automatically sweep this credit.

The injected tests cover two batches, viem encoding/signature vectors,
compatible delegation reuse, forced replacement, changed sender code,
changed keys/nonces/plans, failed journal writes, excessive fee quotes,
ambiguous replies, mismatched transaction data, missing events, and failed
inclusion checks. Those injected tests do not use funds. Separate finite
[Sepolia ETH execution results](SEPOLIA_LIVE_TESTS.md) cover one- and two-note
plans, including real sequential cancel/resume. They do not cover ERC-20
Tornado pools or maximum-size batches. These routes remain experimental;
their C/OS/HTTP effects and end-to-end fund safety are not formally proved.
RPC values remain claims from the configured endpoint, not chain consensus.

## Existing deposit files

An exclusive-create conflict means the named file already exists, not that it
is safe to remove. Deposit errors identify whether it is the sender lock, a
permanent commitment claim, or the journal, and print its exact path. Existing
files remain unchanged. Sender locks may protect pending or unfinished attempts;
commitment claims normally remain after success to prevent duplicate funding.
Inspect the original journal with `deposit status` and reconcile recorded hashes.
Use `--resume` below for supported sequential ETH plans. Do not delete all
Tornado dotfiles to make a new attempt pass admission.

## Resume a sequential ETH journal

`deposit send --resume --journal <original-path>` accepts the same original notes and sender, with `--dry-run` for a read-only reconciliation preview or `--broadcast` to continue. It compares the complete ordered plan with the protected journal, checks every recorded hash against exact successful receipts, indexed EIP-1559 calls, canonical block headers and Deposit events, and checks commitment registration. It requires a recorded prefix followed by an unexposed planned suffix. Pending, unknown, reverted, mismatched or missing evidence stops new signing. Confirmed steps are skipped; every new hash is durably reserved by compare-and-replace before exposure. Existing claims must match the original journal. Recorded claims cannot be recreated when missing; missing planned claims can be admitted for the never-exposed suffix. Completion releases only the matching sender lock. It does not authenticate RPC consensus or make one inclusion final. Legacy token approvals and 4337 batch journals are rejected rather than guessed.
