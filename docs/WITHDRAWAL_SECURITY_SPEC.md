# Withdrawal security specification and evidence

This is best-effort verification of selected properties of the executable.
It does **not** guarantee bug-free code, loss-free withdrawals, or anonymity.
The rules below are the intended user-facing security contract. Each has a
specific implementation and a deliberately limited proof claim.

## Reviewed intent and executable exposure

The sponsored one-note and smart-account batch runner uses
[`WithdrawalDriver`](../Tornado/Runtime/WithdrawalDriver.lean). It dispatches
approval, freshness checks, revalidation, one signing attempt, reservation, exposure
marking, optional signed simulation, one submission and status marking.
[`WithdrawalSend`](../Tornado/Cli/WithdrawalSend.lean) passes its actual
builder result into that machine, carrying the builder equality as evidence.
This machine is used by the runnable CLI, rather than being a separate model
of how it ought to run.

The rules are:

- Approval and successful revalidation precede signing. The review must still
  be within its five-minute window at the three clock checks.
- Signing may change only the account signature in the reviewed operation.
  The signer must report the reviewed owner. The direct route's separate
  EIP-7702 authorization must select the reviewed chain, pinned delegate and
  nonce zero; the batch route accepts no such authorization.
- Reservation receives the complete canonical executable JSON bytes,
  including the separate authorization. A UserOperation hash alone is
  insufficient because it excludes signature material.
- Successful reservation and exposure marking precede any final signed
  simulation or bundler submission. The reservation callback must finish
  writing **all selected note paths** before acknowledging success.
- A failed reservation or exposure mark stops network dispatch. A failed
  signed simulation, lost send reply, wrong reply hash or failed submission
  status write leads to uncertainty and never to a replacement send.
- Within one invocation, the signing callback and submission callback each
  have one slot. Direct signing returns both an operation signature and a
  separate authorization signature in that one attempt. Unknown outcomes
  are terminal for that invocation.

The kernel-checked statements are in
[`WithdrawalDriverProofs`](../Tornado/Spec/WithdrawalDriverProofs.lean).
They constrain the machine's commands, replies, canonical payload and callback
trace. Reachability proofs cap sign, simulation and send invocations at one
each, including failed callbacks. Every dispatched signed network command
has the successful review, revalidation, signing, reservation and exposure
marks in its earlier trace. Once signing is accepted, subsequent responses
preserve the exact full payload. The small IO interpreter dispatches those
commands. Callback success
is an explicit contract: Lean does not prove that a disk write became durable,
that a signer used the expected key, or that a callback avoided other effects.
Protected journal implementations and fault tests provide additional evidence
for those contracts. A crash inside a callback is outside the completed
callback trace; the protected reservation is the recovery mechanism.

The direct builder additionally decodes its own sponsor tuple through
[`DirectWithdrawalIntent`](../Tornado/Protocol/DirectWithdrawalIntent.lean).
An accepted result proves the decoded pool, recipient, fee, proof, root and
nullifier hash equal the selected inputs, the gas fields match the selected
policy, and the direct operation has no execution calldata or execution gas.
The tuple must re-encode to the exact complete input bytes. This is a
field-level property, independent of hash collision resistance. It does not
prove that the user's supplied address is the address they meant to enter.

For batches, [`BatchWithdrawalIntent`](../Tornado/Protocol/BatchWithdrawalIntent.lean)
independently decodes the complete account, sponsor and factory payloads.
The actual public builder's `batch_success_decodes` theorem binds those
decoded fields to original note requests, catalog denominations, account,
owner, gas policy and ordered user calls. The generated withdrawal prefix
contains all nonsponsoring notes in order with zero fee/refund; its only
suffix is the exact reviewed calls or the selected ETH/ERC-20 net forwarding.
User-approved tail calls can themselves interact with arbitrary contracts.

[`ReviewBatchIntent`](../Tornado/Spec/ReviewBatchIntent.lean) connects this
builder theorem to the prepared review used by the runnable driver. Signing
preserves that operation structurally. These are encoded-intent properties,
not correctness of arbitrary target contracts: a preserved, approved call
can still spend assets or grant permissions.

The runner proof covers sponsored 4337 withdrawals. Relayer, deposit,
recovery, status reconciliation and the batch call builder have their own
validators, selected theorems and fault tests; this runner proof does not
extend automatically to their entire execution. Across restarts, protection
depends on preserving the protected journals and using the same status
directory. Separate copies or deleted journals are not globally coordinated.

The machine's `submitted` result means that the bundler acknowledged the
expected operation hash. It does not mean the withdrawal succeeded. The outer
runner still requires matching receipt and pool/EntryPoint events, and rechecks
one observed inclusion before releasing its owner lock. Those
checks do not authenticate Ethereum consensus or prove finality.

## Secret handling and allowed disclosures

The real worker dispatcher constructs a restricted
[`WorkerProgram`](../Tornado/Runtime/WorkerProgram.lean). Its available effects
are reading the configured protected note, the configured bounded request,
four fixed asset slots, and 32-byte entropy draws in proof mode. There is no
network, arbitrary-path read, file-write or logging instruction in that
language. Core-dump suppression is attempted before any read or entropy
access; failure stops evaluation.

The terminal gate permits a canonical typed response or a fixed failure
diagnostic. Proofs and note-derived signatures must pass their request-binding
checks before release. The actual entry point uses this gate. See
[`WorkerDisclosure`](../Tornado/Spec/WorkerDisclosure.lean) and the injected
failure tests in [`WorkerDisclosure.lean`](../tests/WorkerDisclosure.lean).

Allowed parent-local disclosures are note metadata, public signer identity,
request-bound signatures, and proof bytes with six public signals. Raw note
preimages, mnemonics, witness arrays and blinding scalars have no dedicated
output constructor. **This is capability and output-format confinement, not
a zero-knowledge or noninterference theorem.** A malicious or faulty
cryptographic computation could still encode information in an allowed proof,
signature or metadata field. Success/failure, time, resource use, crashes and
memory remnants can also reveal information. Those channels are not proved
secret independent. The installed worker, native interpreter, compiler,
runtime and OS remain trusted.

The trusted parent intentionally learns the association between a selected
commitment, nullifier hash, path, recipient and status record. Public field
values do not make this association harmless. Do not log worker requests or
responses or disclose the local journals unnecessarily.

## Fresh proof randomness

The runtime sampler and worker use the same bounded rejection loop as the
finite draw-tree model in
[`BlindingDistribution`](../Tornado/Spec/BlindingDistribution.lean) and
[`BlindingPair`](../Tornado/Spec/BlindingPair.lean).
[`BlindingBounds`](../Tornado/Spec/BlindingBounds.lean) instantiates the actual
field and retry limit, bounding scalar exhaustion by `2^-128` and pair
exhaustion by `2^-127` under that same ideal entropy contract.
Zero and candidates at or above the scalar-field order are rejected rather
than reduced modulo the order. Each scalar has at most 512 attempts; the
second scalar starts with fresh draws after the first succeeds.

[`ByteEntropy`](../Tornado/Spec/ByteEntropy.lean) proves that the actual 32-byte
decoder is a bijection and transfers byte-product counts to every event of
the existing shared sampler model. The distribution results are conditional
on independent uniform 32-byte inputs independent of the note/witness.
They concern the sampler, including its exhaustion
outcome, rather than assuming successful sampling or assigning a uniform
distribution to its result. The OS entropy source is an assumption, not a
Lean axiom or a proved property of the host. See
[`PROOF_BLINDING_SCOPE.md`](PROOF_BLINDING_SCOPE.md) for precise statements.

The mathematical `SamplerField` bridge also proves the actual canonical
scalar-to-field bijection and arbitrary-event pushforward, including the
common retry-failure mass. For compatible ideal witness offsets under one
public setup, full-field mask observations have exact equal counts; nonzero
mask observations satisfy the explicit `4q/(q−1)²` event bound. The bounded
statement includes failure and does not condition it away.

The [application theorem](../app-proofs/TornadoProofs/WorkerPrefix.lean)
now relates that observation to the original proofProgram, including actual
native assembly, normalization, serialization, compiled-key verification,
request validation and terminal stdout/stderr/exit status. Under its explicit
original-input admission, source and honest-setup conditions, the event bound
is at most `2^-251` for the same public setup and public signals. Later proof
failures and exhaustion remain visible and counted. This does not certify
arbitrary note-parser failures, other worker modes' outputs, physical partial
writes, timing, resource use, crashes or retained memory.

## External API and privacy assumptions

Network responses may be arbitrary bytes within the transport limits.
Parsers reject malformed, oversized, noncanonical or inconsistently bound
data. Proof and receipt checks bind accepted values to selected public
inputs. These are useful guarantees even for hostile responses: a provider
cannot bypass a local acceptance rule merely by returning unexpected JSON.

An internally consistent invented chain can still pass these checks.
Ethereum state, inclusion and finality are not authenticated against a
locally verified consensus root. TLS authenticates the configured server,
not its chain claims. One RPC-observed inclusion is not consensus finality and can be reorganized.
Provider completeness, the selected deployed contracts, cryptographic
security and physical storage behavior remain assumptions. A provider can
also deny service, delay a withdrawal or cause safe rejection; there is no
liveness or successful-withdrawal guarantee for every valid note.

**The configured history RPC is trusted with deposit–withdrawal linkage.**
Current history validation requests the selected deposit transaction receipt
and queries the selected nullifier's spent status. An operator able to
associate those requests with the same client can correlate the deposit and
the prospective or eventual withdrawal, including before the nullifier is
spent. Keeping these checks does not provide query privacy. Proxying them
does not itself prevent the proxy or upstream operator from correlating them.
Final signed batch simulation additionally gives its RPC an executable
operation that it could relay. Reservation and uncertainty handling address
that execution risk, not provider anonymity.

## Completeness and zero knowledge

The full-size public fixtures demonstrate native proof generation accepted
by the native compiled-key verifier and deterministic byte agreement with
the pinned SDK. A successful Classic pipeline result now carries exact
provenance from its original assets, withdrawal input and supplied blinding,
through input-prefix construction, the actual witness generator, key decoding,
H, point assembly, serialization and reviewed public signals. This proves what
produced a returned result, not that every independently valid input succeeds.

The [proof-only workspaces](../proofs/README.md) certify the actual field
primes, extension towers, all admitted FFT/IFFT sizes, sparse H/QAP
construction, G1/G2 groups and scalar/MSM loops, normalization, complete
Groth16 assembly and exact eight-limb byte encoding. The reduced Tate pairing
has derived bilinearity and a closed nontrivial-generator certificate. Native
verifier completeness and scalar-equation equivalence are proved under
explicit setup/key spans and the executable's finite-point conditions.

The public circuit certificate and independent point-schedule gate run before
secret input. Source-level witness constructions derive execution, ordered
complete assignment and every R1CS check from explicitly stated original
input conditions. `prepareInputPrefix_iff_source` proves those conditions
characterize actual accepted inputs, including all path directions and the
native parent computation. `native_construct_accepted_witness` constructs
the complete canonical witness and every row check; its source-to-circuit
Pedersen agreement is proved from the actual note bytes and public generator
receipts, rather than assumed. Public digests authenticate bytes; they do
not establish an honest setup or a deployed contract's identity.

The conditional statistical theorem concerns proof output after valid
admission, with all later failures counted. It is not full physical-process
zero knowledge. The secret-bearing Lean arithmetic remains variable time and
nonzeroizing; OS entropy, compiler/runtime behavior, side channels, truthful
chain evidence and expected deployed contracts remain trust boundaries. No
funded transaction is part of the verification gate.

To review the specification, compare these rules with the linked definitions
and theorem statements, then inspect the explicit assumptions. Run
`node scripts/verify.mjs --kernel-only` for all workspace builds and axiom
checks, or `node scripts/verify.mjs` with Node 22.18 or newer for the broader
offline gate. `lake build Tornado` alone does not check the separate Mathlib
workspace; see [verification setup](VERIFICATION.md). Its report inventories
theorems, allowed standard axioms, exact input hashes and test coverage;
`PASS_WITH_LIMITATIONS` means those checks passed, not that the entire CLI is
certified safe.
