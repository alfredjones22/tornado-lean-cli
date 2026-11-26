# Security specification

This is the intended security contract for the native CLI. It is best-effort
verification of selected properties, not a guarantee of bug-free software,
loss-free operation or anonymity. A rule stated here is not automatically a
proved property of every command. [Proof coverage](PROOFS.md) identifies the
definitions, theorem statements, finite tests and remaining gaps.

## Reviewed intent

A review fixes the chain, pools, selected note identities, recipient, amount,
fees, account, nonce, deployment policy and ordered post-withdrawal actions.
The CLI should sign only the operation produced by that review:

- Approval and successful revalidation precede signing. Sponsored withdrawal
  reviews must remain within their five-minute window at the driver's three
  clock checks.
- A signature may change only the account signature in the reviewed
  UserOperation. The signer must identify the reviewed owner.
- Direct one-note 4337 authorization must select the reviewed chain, pinned
  delegate and nonce zero. The smart-account batch route admits no separate
  EIP-7702 authorization.
- Gas estimates precede real proofs and use dummy proofs, signatures and
  authorizations. Real proof generation follows bounded quote convergence.
- After slow proving, history, known roots, account state and current fee
  bounds are revalidated before final review. Eligible direct withdrawals
  and batches without custom calls may lower their gas bid at this stage;
  proofs, note fees, payouts, forwarding amounts and all gas limits remain
  unchanged. Custom calls retain the original bid because of `GASPRICE`.
- Checks after final review must not silently change the reviewed gas bid,
  fee, proof or operation. If a current bid cannot fit the prepared budget,
  preparation stops rather than increasing the authorization.

The direct builder's independent decoder binds the pool, recipient, fee,
proof, root, nullifier and gas policy to the selected inputs. It requires
empty execution calldata and zero execution gas. Canonical re-encoding must
recover the exact complete sponsor-tuple bytes, not merely a matching hash.
See [DirectWithdrawalIntent](../Tornado/Protocol/DirectWithdrawalIntent.lean).
These checks preserve the entered address; they cannot determine whether it
is the address the user intended to enter.

## Batch withdrawal semantics

A complete reviewed batch must decode to:

1. One sponsoring withdrawal during paymaster validation. It pays the selected
   positive fee and sends the remaining denomination to the reviewed account.
2. Every nonsponsoring withdrawal exactly once and in selection order, with
   zero relayer, fee and refund, paying that same account.
3. The exact ordered user calls, when supplied. Otherwise, optional ETH or
   token forwarding equal to the sum of denominations minus the sponsor fee,
   paying the reviewed external recipient.
4. The selected owner and pinned salt in any required factory deployment,
   together with the reviewed account nonce and gas/fee fields.

Independent canonical decoders reject extra calls, trailing data, overlapping
dynamic regions, nonzero ABI padding and changed fields. The actual public
builder's `batch_success_decodes` result binds those semantics to original
note requests and catalog amounts. `prepared_batch_decodes` connects that
result to the review used by the runnable driver; signing preserves it.
See [BatchWithdrawalIntent](../Tornado/Protocol/BatchWithdrawalIntent.lean),
[SponsoredWithdrawal](../Tornado/Protocol/SponsoredWithdrawal.lean) and
[ReviewBatchIntent](../Tornado/Spec/ReviewBatchIntent.lean).

This specifies encoded intent, not arbitrary target contracts' business
logic. An approved call can spend assets or grant permissions. A later
execution failure can leave the sponsor note spent and funds in the
recoverable account: paymaster validation and account execution are not an
all-notes-or-nothing deposit/withdrawal guarantee.

## Backups and deposit correspondence

For locally created notes, admitted serialization and parsing must preserve
the exact preimages, selected pools, note order and seed-recovery data.
Funding commitments must be the native commitment function applied to those
preserved preimages. Each signed deposit must target the selected pool and
commitment, with the denomination as ETH value for an ETH pool, or zero ETH
value for a token pool. Token approvals must be bounded by the selected
per-pool totals.

Distinctness must be admitted or validated explicitly; random generation
does not make collisions logically impossible. Correct backup correspondence
does not itself establish equivalence to a deployed commitment primitive or
withdrawal circuit. A public-invoice payer instead approves the reviewed
commitment and need not possess its secret note. The payer cannot infer that
the intended recipient retained a valid backup.

Simple7702 deposits require a distinct approval for persistent delegation
when installing or replacing it. Its signed authorization is recorded before
estimation can receive it; cancellation after that exposure does not revoke
the authorization. Final deposit-batch approval is separate.
See [DepositBackupIntent](../Tornado/Spec/DepositBackupIntent.lean) and
[DepositIntent](../Tornado/Protocol/DepositIntent.lean).

## Reservation before executable exposure

Before a proof-bearing relayer POST, signed final simulation or submission,
preserve the full canonical executable candidate and every required local
claim. A batch must reserve every selected note. A UserOperation hash alone
is insufficient when signatures or separate authorization are excluded from
that hash.

The sponsored runner uses the actual
[WithdrawalDriver](../Tornado/Runtime/WithdrawalDriver.lean), interpreted by
[WithdrawalSend](../Tornado/Cli/WithdrawalSend.lean). Its proof constrains the
commands and callback trace:

- Approval, revalidation and signing precede successful reservation; exposure
  marking follows reservation and precedes signed network dispatch.
- The reservation callback must finish all selected note writes before it
  acknowledges success. Failed reservation or exposure marking blocks the
  network command.
- Within an invocation, signing, signed simulation and submission have at
  most one callback slot each, including failed callbacks. Direct signing
  returns operation and authorization signatures in its single attempt.
- Once signing is accepted, later responses retain the same full payload.
- Failed signed simulation, lost send replies, wrong reply hashes and failed
  outcome persistence lead to uncertainty, never a replacement send.

See [WithdrawalDriverProofs](../Tornado/Spec/WithdrawalDriverProofs.lean).
A callback acknowledgement is a contract: those theorems do not prove disk
durability, native signer behavior, or the absence of extra callback effects.
A crash inside a callback is outside the completed trace. Conditional
filesystem/crash models and fault tests add evidence for the actual journal
adapter; [recovery](RECOVERY.md) states their scope.

After interruption, retain candidate bytes, all reservations and any batch
in-progress marker. A write can complete while its reply is lost. Only exact
reconciliation may classify success or release a lock. Copies of directories,
manual deletion and hostile same-user modification are outside coordinated
local exclusion. Availability and eventual mining are separate properties.

The sponsored runner proof does not automatically cover the entire relayer,
deposit, recovery or status-repair command. Their validators, selected proofs
and fault tests have the narrower coverage listed in [PROOFS.md](PROOFS.md).
Older policy/effect models remain separate from the runtime driver; a raw
abstract confirmation action has no exact-receipt guarantee unless its
explicit event bridge is used.

## What counts as success

A bundler acknowledgement, relayer job identifier or timeout does not prove
withdrawal success. Confirmation requires the exact expected transaction,
successful receipt and matching pool events; sponsored routes also require
the matching successful EntryPoint/UserOperation evidence. Every selected
withdrawal must match for a batch. A saved status observation is distinct from
a successful transaction and from complete persistence of every status mirror.

Send commands accept one validated observed inclusion before proceeding or
releasing the relevant owner lock. There is no further twelve-block wait.
That observation can be reorganized; it is not authenticated finality.
Providers can deny service or cause safe rejection, so there is no guarantee
that every valid note will successfully withdraw through an arbitrary API.

## Secret handling and allowed disclosures

The trusted parent may receive selected-note metadata, public signer
identity, request-bound signatures, proof bytes and the six public signals.
It intentionally learns associations among commitment, nullifier hash,
Merkle path, recipient and status record. Do not log worker requests/responses
or disclose local journals unnecessarily.

The actual [WorkerProgram](../Tornado/Runtime/WorkerProgram.lean) admits only
configured note/request reads, four fixed asset slots and proof-mode entropy
draws. Its effect language has no network, arbitrary-path read, file-write or
logging operation. The terminal gate allows one canonical typed response
line or one fixed failure diagnostic. Proof/signature release repeats request
binding. [WorkerDisclosure](../Tornado/Spec/WorkerDisclosure.lean) proves those
capability and output-format restrictions for the dispatched program.

Those restrictions alone do not prove that allowed cryptographic outputs
cannot encode secrets. They provide no general secrecy theorem for metadata,
signatures, time, resource use, crashes or memory remnants. The installed
worker and native interpreter remain trusted.

## Randomness and conditional proof-output privacy

The entropy contract supplies independent uniform 32-byte draws, independent
of note/witness values. The actual decoder bijection and canonical
scalar-to-field transport are proved. The runtime uses bounded rejection,
not modular reduction: zero and values outside the scalar field are rejected,
with at most 512 attempts per scalar and fresh draws for the second scalar.
Under that ideal entropy contract, scalar exhaustion is bounded by `2^-128`
and pair exhaustion by `2^-127`.

The model includes exhaustion rather than conditioning it away. For compatible
ideal witness offsets under one public setup, full-field mask observations
have equal counts, while nonzero-mask observations have an explicit
`4q/(q−1)²` event bound. Sampler uniformity alone is not a theorem about a
subsequently released proof.

The application proofs connect the actual proof program to native assembly,
normalization, serialization, compiled-key verification, request validation
and terminal stdout/stderr/exit status. Under original-input admission, source
composition and honest-setup/key hypotheses, they derive a `2^-251` event
bound against an explicit witness-free reference. A companion theorem bounds
differences between two admitted contexts with the same setup and public
signals. All later proof failures and exhaustion remain counted.

See [WorkerPrefix](../app-proofs/TornadoProofs/WorkerPrefix.lean),
[OutputSimulation](../app-proofs/TornadoProofs/OutputSimulation.lean) and the
[application workspace](../app-proofs/README.md). The reference uses abstract
setup trapdoors; it is not an efficient public simulator or a trapdoor-recovery
algorithm. These
results exclude arbitrary note-parser failures, other worker modes, physical
partial writes, timing, memory and crashes. They are not full physical-process
zero knowledge or an anonymity guarantee.

## Reading the evidence

An acceptance theorem explains what follows when a checker returns success.
A construction theorem derives an implemented result from independently
stated valid-input conditions. Neither should be presented as the other.
Successful pipeline provenance identifies the exact assets, input, witness,
H, key queries and serialization that produced a returned result; it does not
prove that every independently valid input succeeds.

Source-level witness constructions and public circuit certificates connect
accepted original inputs to the complete canonical assignment and every
pinned R1CS row. Field/group/FFT/H/assembly/pairing and verifier-completeness
results retain their explicit source, setup, key and finite-point conditions.
Digests authenticate bytes, not an honest ceremony or deployed contract.

Review the actual statements linked by [PROOFS.md](PROOFS.md), then the
[trust assumptions](TRUST_BOUNDARIES.md). [VERIFICATION.md](VERIFICATION.md)
explains how to reproduce axiom checks and regression evidence. Passing them
does not certify complete command correctness, cryptographic hardness,
physical secret safety or truthful Ethereum state.
