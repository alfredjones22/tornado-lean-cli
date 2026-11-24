# Security contracts

These contracts specify the intended behavior independently of individual
encoders, validators and effect adapters. They are not a claim that every
contract is already proved. The current evidence and limits are recorded in
[the proof scope](PROOF_SCOPE.md) and
[the withdrawal specification](WITHDRAWAL_SECURITY_SPEC.md).

## Batch withdrawal intent

A reviewed batch fixes its chain, selected pools and note identities, account,
owner, nonce, deployment policy, recipient, sponsor fee, gas policy and ordered
user calls. Interpreting the complete encoded operation must yield:

1. One sponsoring withdrawal during paymaster validation, paying the selected
   positive fee and sending the remaining denomination to the reviewed account.
2. Each remaining selected withdrawal exactly once and in selection order,
   with zero relayer, fee and refund, paying the same reviewed account.
3. The exact ordered user calls, if present. Otherwise, an optional ETH or
   token transfer of the sum of selected denominations minus the sponsor fee
   to the reviewed external recipient.
4. The selected owner and pinned salt in any required factory deployment,
   and exactly the reviewed account nonce and gas/fee fields.

Canonical parsing rejects extra calls, trailing data, overlapping dynamic
regions, changed public fields and nonzero ABI padding. The intent concerns
what is encoded. Arbitrary user-approved target contracts can spend assets
or grant permissions, and their business logic is not certified by this
contract. A later execution failure can leave the sponsoring note spent and
funds in the recoverable account.

## Backup and deposit correspondence

For locally created notes, serializing and parsing an admitted backup must
preserve the exact preimages, pool selection, order and seed recovery data.
The commitments selected for funding must be the native commitment function
applied to those preserved preimages. Every signed deposit must target the
selected pool, carry that commitment, and have the selected denomination as
ETH value for an ETH pool or zero ETH value for a token pool. Token approvals
must be limited to the selected per-pool totals.

Distinctness is an admitted condition or an explicit validation result;
random generation does not make collisions logically impossible. This
correspondence does not by itself prove that the commitment primitive or
withdrawal circuit matches deployed Ethereum code. Public-invoice payment
instead binds the reviewed invoice; the payer need not hold its secret note.
The 7702 route has a distinct approval for persistent authorization exposed
during estimation, in addition to final deposit-batch approval.

## Executable exposure and recovery

Before any proof-bearing relayer POST, signed final simulation or submission,
the implementation must preserve the complete executable candidate and the
required local claims. For a batch, every selected note must be reserved.
Hash-only association is insufficient when a separate authorization exists.

Persistence contracts permit an operation to complete and then report failure.
Every interrupted prefix must retain enough evidence to block replacement
after an exposure might have occurred. Partial mirror repair must preserve
candidate bytes, note reservations and the authoritative in-progress marker.
Only the specified exact receipt/event reconciliation may release a lock or
classify success. A bundler acknowledgment, relayer job or timeout does not
establish successful withdrawal.

These properties apply within one coordinated local status/key directory.
They do not provide global exclusion across copied directories, manual
deletion or a hostile same-user process. Physical durability is conditional
on the documented protected filesystem boundary. Availability and eventual
mining are separate from preservation of an uncertain attempt.

## Construction and accepted results

An acceptance theorem states what follows when a native checker returns
success. A construction theorem starts from independently defined valid-input
conditions and establishes the result produced by the implemented algorithm.
Both are useful, and the evidence must identify which statement is proved.

For witness/proof construction, validity names the note relation, Merkle path,
public statement, field bounds, circuit and required key/setup relations.
Field, curve, polynomial, witness, serialization and verifier correspondence
are separate implementation obligations. The current proof workspace closes
specified native field, G1 add/double/normalization, root/butterfly/two-point
and fixed-limb encoding results. Successful actual G1 windowed MSM calls now
have exact original-input weighted-sum and normalization theorems. General
witness-gadget correspondence, FFT/H/QAP, group/subgroup order, G2 MSM/group
and pairing correspondence remain
unclosed. A pinned digest authenticates bytes;
it does not establish the mathematical relationship between a circuit and
the key's polynomial/query tables or establish an honest ceremony.

## Allowed disclosures and entropy

The trusted parent may receive selected-note metadata, signer identity,
request-bound signatures, and proof bytes with public signals. The configured
history RPC is trusted with the deposit--withdrawal association revealed by
selected receipt and nullifier-spent queries. These associations are privacy
sensitive and are not an anonymity guarantee.

A proof-output privacy statement fixes the admitted public statement and
allowed metadata and includes failure as an observation. It must account for
the implementation's nonzero scalar restriction, bounded rejection sampling,
infinity rejection and later failures. Conditional sampler uniformity alone
does not establish the distribution of a subsequently released proof.

The entropy contract supplies independent uniform fixed-width byte strings,
independent of note/witness values. The actual fixed-width decoder bijection,
canonical scalar-to-field bijection and arbitrary-event sampler pushforward
are proved. Under this source contract, compatible ideal witness offsets
satisfy an explicit nonzero-mask observation bound with common retry failure
included. The full worker's released observations and additional failures
are not proved to factor through that ideal model. OS randomness remains a
boundary assumption. Timing, allocation, crashes and
memory remnants require a separate threat model; the current variable-time,
nonzeroizing Lean arithmetic has no such secrecy certificate.

## Mathematical dependency and proof policy

The executable and proofs use Lean 4.29.1. The installed proof-only workspace
uses Mathlib release `v4.29.1`, immutable revision
`5e932f97dd25535344f80f9dd8da3aab83df0fe6` from
`https://github.com/leanprover-community/mathlib4`, with pinned transitive
revisions. Its checked bridges relate selected actual native operations to
mathematical field, group and finite-count models. The runnable CLI and the
pure `LeanCrypto` package do not import Mathlib. Manifests and fresh verification
reports identify the exact checked dependency and source inventory.
When official precompiled Mathlib caches are used, imported dependency/build
artifacts and the compiler remain trusted; compiling the project proofs does
not establish a fresh source reconstruction of every dependency.

Any introduced dependency must be pinned with its transitive revisions and
checked proof assumptions. No new global axiom may stand for correctness or
privacy of the implementation. Honest cryptographic setup, compiler/runtime,
OS and external chain evidence must remain separately visible assumptions.
Malformed or inconsistent bounded API replies can be rejected locally; an
internally consistent fabricated chain cannot be authenticated by parsing.
