# Proof coverage and evidence

This is best-effort verification of selected native definitions. It does not
certify bug-free software, loss-free transactions, anonymity or side-channel
safety. The [security specification](SECURITY_SPEC.md) states the intended
rules; this guide identifies which parts have proofs, tests or assumptions.
See [verification instructions](VERIFICATION.md) to reproduce the evidence.

## How to read a claim

- An **acceptance theorem** establishes what follows when a particular native
  checker or builder succeeds. It need not show that valid inputs succeed.
- A **construction theorem** starts with independently stated input conditions
  and derives the original algorithm's return. Read those conditions: they may
  include valid key/query relations, degree bounds or finite-point conditions.
- A **finite test** checks examples, mutations or fault schedules. It is useful
  independent evidence, but does not establish a statement for all inputs.
- A **physical assumption** concerns a compiler, OS, device, entropy source,
  network service or deployed contract. A theorem over supplied data does not
  authenticate those external facts.

The executable's definitions are imported by the proofs. Proof erasure removes
logical fields at runtime; it does not erase secret data from process memory.
Successful axiom inspection also does not mean a theorem has no hypotheses.

## Workspaces and proof policy

The CLI and reusable [LeanCrypto package](../packages/lean-crypto/README.md)
contain native code and selected proofs. The separate
[mathematical workspace](../proofs/README.md) relates the actual arithmetic to
Mathlib models. The [application workspace](../app-proofs/README.md) composes
those results with the original witness generator and worker program.
The executable and portable runtime package do not depend on Mathlib.

The verifier builds all three workspaces, inspects every named theorem's axiom
report and rejects proof escapes and custom axioms. The permitted standard
axioms are `propext`, `Classical.choice` and `Quot.sound`. Lean is pinned to
4.29.1; Mathlib and transitive revisions are pinned in their manifests.
Official precompiled Mathlib caches are trusted imported artifacts, rather
than a fresh source rebuild of every dependency.

## Reviewed intent, exposure and command behavior

[`WithdrawalDriver`](../Tornado/Runtime/WithdrawalDriver.lean) is the command
machine interpreted by the actual sponsored sender in
[`WithdrawalSend`](../Tornado/Cli/WithdrawalSend.lean).
[`WithdrawalDriverProofs`](../Tornado/Spec/WithdrawalDriverProofs.lean) constrains
approval, freshness checks, revalidation, signing, reservation, exposure,
optional final signed simulation and the single submission. `PreparedReview`
retains equality to the actual builder result. `FinalPayload` binds the whole
serialized operation and separate EIP-7702 authorization, permitting only the
specified signature change. Unknown terminal outcomes block a new attempt.

These results concern the runtime-used machine and its callback contracts.
They do not prove physical callback effects, filesystem durability, arbitrary
extra effects or every deposit, recovery and relayer command. A signed
simulation is executable exposure; its RPC can relay the operation.

Independent semantic gates constrain what the builders encode:

- [`DirectWithdrawalIntent`](../Tornado/Protocol/DirectWithdrawalIntent.lean)
  binds direct withdrawal fields and canonical sponsor bytes, and excludes
  direct execution calls.
- [`AbiDecode`](../Tornado/Protocol/AbiDecode.lean) independently decodes
  withdrawals, composed batches, transfers and the pinned factory call.
  Canonical reencoding rejects alternate offsets, overlapping regions,
  padding and trailing bytes.
- [`BatchWithdrawalIntent`](../Tornado/Protocol/BatchWithdrawalIntent.lean)
  compares those meanings with the original input. `batch_success_decodes`
  constrains the actual sponsored builder's result: sponsoring withdrawal,
  ordered remaining withdrawals, exact suffix or net forwarding, deployment
  and gas policy. [`ReviewBatchIntent`](../Tornado/Spec/ReviewBatchIntent.lean)
  carries that result into the prepared review and final payload.
- [`DepositIntent`](../Tornado/Protocol/DepositIntent.lean) certifies the
  actual planners' ordered commitments, denomination-valued ETH deposits,
  zero-valued token deposits, exact approvals, chunking and route selection.
  `checked_ordered_funding` and `checked_routing` expose those statements.
  Both sequential adapters check their final serialized transaction.
  [`DepositCallsIntent`](../Tornado/Protocol/DepositCallsIntent.lean) separately
  checks the actual Simple7702 execute/batch bytes.
- [`WithdrawalNetwork`](../Tornado/Cli/WithdrawalNetwork.lean) proves
  `lowerGasBid_ethFee_nonincreasing`: admitted downward bid changes cannot
  increase the modeled maximum ETH gas fee. This does not authenticate the
  RPC's fee references or prove a bundler will accept the operation.

These are encoding and acceptance properties, not proofs of arbitrary user
contract semantics or universal successful construction. In particular, the
separate signed 7702 delegation is not cryptographically limited to a deposit.
It has its own review and durable uncertainty record before estimation.

## Reservation, replay and restart

The actual [`WithdrawalJournal`](../Tornado/Cli/WithdrawalJournal.lean)
uses a finite protected-file interpreter. Exact mirror acknowledgements must
precede memory-state advancement. Its conditional physical-model bridge
establishes exact stored candidate bytes after a complete reservation and
readmission blocking after modeled interruption. Partial records and metadata
errors are conservatively occupied, not permission to retry. Batch repair
checks serialized reservation identity before compare-and-replace updates.

The separate [`Attempt`](../Tornado/Spec/Attempt.lean),
[`Refinement`](../Tornado/Spec/Refinement.lean) and
[`EffectRefinement`](../Tornado/Spec/EffectRefinement.lean) describe earlier pure
policy/driver models. They prove reviewed-hash binding, reservation before
exposure, send caps and exact-evidence confirmation under supplied durable-write
acknowledgements and authentication results. These models must not be mistaken
for a complete refinement proof of every runnable adapter.

[`AttemptJournal`](../Tornado/Runtime/AttemptJournal.lean) and
[`NoteClaims`](../Tornado/Runtime/NoteClaims.lean) have tested IO adapters and
pure replay/claim-name theorems. [`JournalIORefinement`](../Tornado/Spec/JournalIORefinement.lean)
constrains the loader's actual `replayRecord`: identity, sequence, required
reservations, send-slot consumption and immediate second-send rejection.
These do not prove all filesystem effects or identify this example journal
with every sender's journal. The [recovery guide](RECOVERY.md) distinguishes
runtime-used reservation/restart guarantees, status repair and their limits.

## Backups, plans, parsing and chain evidence

[`CatalogProofs`](../Tornado/Domain/CatalogProofs.lean) checks the native 29-pool
catalog: 20 mainnet pools, nine Sepolia pools, positive amounts and unique
addresses. It does not authenticate deployed contracts.
The runtime plan validator proves exact requested-value conservation and
checks permitted entries/counts. It does not prove planner optimality on all
inputs; the 1,860-cell grid and 900 alternative-plan cases are finite evidence.

[`DepositBackupIntent`](../Tornado/Spec/DepositBackupIntent.lean) constructs the
actual formatter, parser and public-item projection for admitted source
records. Successful independent and seeded constructors supply identity,
hex, grammar and renderer evidence through `Source.ofIndependent` and
`Source.ofSeeded`. Catalog/network, count, same-asset, nullifier-distinctness
and applicable phrase conditions remain explicit. There is no cryptographic
security theorem or all-entropy successful-creation claim. The actual
tail-recursive splitter is proved equivalent to its structural definition.

ABI, typed transaction, UserOperation and receipt modules have exact
encoding/decoding, bounds and binding results. Examples include canonical
sponsor-tuple reencoding, signature-independent EntryPoint v0.8 hashes,
uint128 gas overflow rejection, typed transaction reencoding and stateless
EIP-7702 validity/intent guards. These are not proofs of Ethereum execution.

[`Events`](../Tornado/Protocol/Events.lean),
[`EvidenceBridge`](../Tornado/Policy/EvidenceBridge.lean) and
[`RpcReceipt`](../Tornado/Protocol/RpcReceipt.lean) bind the expected operation,
pool, nullifiers, recipient, fees and transaction/block metadata to exact
decoded events. The pure policy's receipt-success flags and supplied logs
remain caller inputs. The bridges do not establish consensus authenticity,
finality or durable reachability of the supplied policy state.

History guards bound selected pool/ranges and accepted cursors. The reducer
requires contiguous leaf indices, rejects repeated identifiers, and checks
the reconstructed count/root against same-block claims. Sync theorems constrain
captured-head coverage and aggregate-byte limits. Cache persistence and reorg
handling have injected tests, not complete effect proofs. A provider can still
fabricate mutually consistent replies. See [trust boundaries](TRUST_BOUNDARIES.md).

## Witness construction and circuit correspondence

The pinned Classic `Withdraw(20)` circuit uses 31-byte nullifier and secret
components, a 20-parent MiMC path and six public signals. Native generation
computes all 36,528 signals and materializes all 28,300 witness slots, then
checks all 28,275 authenticated R1CS equations. It does not call an external
script or copy a fixture witness at runtime.

[`TornadoWitness`](../Tornado/Protocol/TornadoWitness.lean) constructs the
49-slot input prefix. [`WitnessVM`](../Tornado/Protocol/WitnessVM.lean)
authenticates the typed graph and circuit, checks assignment completeness,
and returns a checked witness. Guard theorems alone say accepted output
passed the checker; the following construction results go further:

1. [`Source.ValidWithdrawal`](../app-proofs/TornadoProofs/Witness/WithdrawalSource.lean)
   independently states original note/path, public-field and root conditions.
2. [`InputInverse.prepareInputPrefix_iff_source`](../app-proofs/TornadoProofs/Witness/InputInverse.lean)
   proves that actual input acceptance is equivalent to that domain.
3. [`ReferenceProgramMeaning.referenceMeaning_construct`](../app-proofs/TornadoProofs/Witness/ReferenceProgramMeaning.lean)
   derives point-operation domains and the actual commitment/nullifier hash
   identities from source facts and checked public generator receipts.
4. [`NativeWitnessConstruction.native_construct_accepted_witness`](../app-proofs/TornadoProofs/Witness/NativeWitnessConstruction.lean)
   constructs actual generation, the canonical full witness, exact reviewed
   signals and every R1CS check. Final witness/checker success is a conclusion.

The public asset gate validates native generator subgroup receipts, circuit
base binding, an independent signed-window schedule, and a full linear
elimination/row-derivation certificate. The certificate checker is proved;
its extractor need not be treated as a mathematical oracle. Native primitive
execution and public compilation are connected to source meanings and rows.
This is about the pinned typed program and R1CS, not a general compiler
equivalence theorem or proof that the circuit expresses every user expectation.
R1CS satisfaction does not establish on-chain note inclusion, unspentness or root age.

Four public full-witness cases exercise every signal, including an exact
28,300-slot reference match, a second leaf, changed note/public inputs and the
rightmost full-depth path. They supplement the source proofs; they are not
four universal theorems or evidence of secure secret handling.

## Arithmetic, Groth16 construction and verification

The [mathematical workspace](../proofs/README.md) proves properties of the
canonical LeanCrypto implementations used by the CLI:

- Certified field/subgroup primes, modular arithmetic, inverses and
  exponentiation, and Fp2/Fp6/Fp12 field representations.
- G1/G2 addition, doubling, scalar loops, normalization and windowed MSMs
  after mapping to mathematical groups. Generator orders use unreduced native
  calculations; normalization uniqueness connects coordinate observations.
- BabyJubJub field and complete Edwards addition, actual Montgomery charts,
  signed-window bounds and noncollision conditions used by native Pedersen.
- [`FFT/NativeTransform`](../proofs/LeanCryptoProofs/FFT/NativeTransform.lean)
  constructs forward/inverse DFT semantics and roundtrip for admitted
  power-of-two sizes through 65,536.
  [`FFT/HConstruction`](../proofs/LeanCryptoProofs/FFT/HConstruction.lean)
  constructs sparse accumulation, transforms, convolution, extraction and
  trimming. Original degree-bounded rows and sparse-table alignment derive
  the QAP quotient and H's domain-minus-one bound, rather than assuming them.
- Complete original Groth16 A/B/C assembly from ordered valid key points,
  canonical scalars and dimensions. Normalization and exact eight-word,
  256-byte serialization, including failures, factor through the ideal
  group-scalar triple.
- Native reduced Tate field embeddings, lines, Miller execution and addition
  laws in both arguments. A checked public arithmetic trace certifies the
  generator pairing is nontrivial.

[`VerifierScalarEquivalence.verify_scalar_iff`](../proofs/LeanCryptoProofs/VerifierScalarEquivalence.lean)
establishes native verifier/scalar-equation equivalence on specified generator
spans and finite canonical inputs.
[`VerifierCompleteness.assembly_qap_verifies`](../proofs/LeanCryptoProofs/VerifierCompleteness.lean)
constructs native acceptance from original assembly/QAP equations, honest
proving/verifying-key relations and explicit finite-point conditions.
Neither final pairing acceptance nor the QAP quotient is simply assumed.
These algebraic results do not prove knowledge soundness, setup honesty,
discrete-log hardness or equivalence to Ethereum's optimal Ate precompile.

[`ProvingKey`](../Tornado/Protocol/ProvingKey.lean) authenticates the complete
14,522,256-byte raw key and parses every pinned section, checking Montgomery
conversion, dimensions, canonical scalars and curve/twist equations.
On-curve parsing alone does not prove arbitrary G2 subgroup membership or
honest query relations. [`ClassicVerifyingKey`](../Tornado/Protocol/ClassicVerifyingKey.lean)
fixes all key coordinates and exactly six public signals/seven IC points;
its wrapper does not accept a caller-selected key. Source/fixture comparison
is finite provenance evidence, not authentication of a deployed pool/verifier.

[`ClassicProofPipeline`](../Tornado/Protocol/ClassicProofPipeline.lean) joins
authenticated compressed assets, input/witness construction, full key decoding,
H, proof assembly, serialization and compiled-key verification. Its success
theorems trace the actual returned bytes to the original input, assets and
supplied blinding. This is execution provenance; construction and verifier
completeness use the separate hypotheses above. Hashing assets proves byte
identity under the hash assumption, not setup honesty or circuit semantics.

## Randomness and conditional proof-output privacy

The actual IO sampler, worker and finite draw-tree model share bounded retry
loops. Each blinding scalar uses separate 32-byte reads, admits only
`1 <= value < Fr`, and has 512 attempts. There is no modulo reduction.
[`BlindingDistribution`](../Tornado/Spec/BlindingDistribution.lean) and
[`BlindingPair`](../Tornado/Spec/BlindingPair.lean) derive exact success/failure
counts and conditional uniformity/independence from sequential execution.
[`ByteEntropy`](../Tornado/Spec/ByteEntropy.lean) proves the full-width decoder
bijection and event transport. `SamplerField` closes canonical Nat-to-field
transport for arbitrary events, retaining retry failure.

Under IID uniform source bytes, conservative exhaustion bounds are `2^-128`
per scalar and `2^-127` for either sequential draw. They exclude OS failures
and later prover failures. Entropy quality and independence are assumptions.

`Groth16IdealPrivacy` fixes a common setup with nonzero delta and compatible
witness offsets. Full-field mask translation gives equal observation counts;
nonzero masks give event difference at most `4q/(q-1)^2`. The application
composition connects actual assembly, normalization, encoding, compiled-key
acceptance, request validation and terminal output to that ideal observation.

[`NativeWorkerReference.native_original_worker_reference_bound`](../app-proofs/TornadoProofs/Witness/NativeWorkerReference.lean)
starts from the real pre-entropy admission prefix, constructs the witness,
and bounds every terminal stdout/stderr/exit-status event relative to an
explicit witness-free reference by `2^-251`. The reference uses abstract
setup trapdoor scalars and public request/signals; it is not an efficient
public simulator or a trapdoor-recovery algorithm. It needs no second witness.
[`WorkerPrefix.original_worker_output_privacy`](../app-proofs/TornadoProofs/WorkerPrefix.lean)
also compares two admitted contexts with the same public setup and signals.
Later proof failures and sampler exhaustion remain in the distribution.

Read [`ExecutionSource`](../app-proofs/TornadoProofs/PipelineComposition.lean)
and [`ProofPrivacy.Context`](../app-proofs/TornadoProofs/ProofPrivacy.lean):
later key decoding, H/context composition, honest query/setup/QAP relations
remain explicit. A successful asset hash does not discharge those hypotheses.
The result excludes malformed-note admission, other modes' cryptographic
contents, physical partial writes, crashes, timing, memory/resources and erasure.
It is not a full physical-process zero-knowledge theorem.

[`WorkerDisclosure`](../Tornado/Spec/WorkerDisclosure.lean) separately proves
mode-specific read/entropy capabilities and typed request-bound output or
fixed failure for the actual restricted worker language. In proving mode,
all four public asset slots are admitted before the note. This confinement does not prove
the physical interpreter or installed executable follows the model.

## Tests and remaining gaps

Finite checks cover hash/key vectors, encodings, input mutations, public
witnesses/proofs, protected IO and injected failures. The local EVM suite runs
actual Classic verifier/account/paymaster code, native builder output and
three public proofs, rejecting changes to each public signal. EntryPoint,
pools, tokens and address/storage placement are synthetic. It does not run
full `handleOps` or certify deployed state. See [verification](VERIFICATION.md).

Hash/signature vectors and selected input guards do not prove every hash,
secp256k1, mnemonic or parsing algorithm against an independent all-input
specification. Constant-time behavior and complete secret erasure are not
proved. Native C/OS/compiler behavior, filesystem durability, truthful chain
evidence, setup honesty, cryptographic hardness, deployed-code identity and
complete command-level refinement remain outside the established results.
The [trust boundaries](TRUST_BOUNDARIES.md) and [build provenance guide](BUILD_PROVENANCE.md)
explain those operational and artifact-integrity limits.
