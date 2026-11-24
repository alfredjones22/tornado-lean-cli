# Application proofs

These are best-effort, kernel-checked statements about selected native CLI
computations. They do not guarantee bug-free code, loss-free transactions,
anonymity or side-channel safety.

This proof-only workspace imports the local CLI and
[`leanCryptoProofs`](../proofs/README.md), using the same pinned Lean 4.29.1,
Mathlib revision and nine transitive Git revisions. The runnable CLI and
portable crypto package do not depend on Mathlib.

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d app-proofs build
node scripts/verify.mjs --kernel-only
```

Resolve and cache the mathematical dependencies using the
[mathematical workspace instructions](../proofs/README.md) first. Lake can
reuse its canonical dependencies; duplicate cached checkouts are unnecessary.
The verification gate checks every local package path and Git revision,
compiles both proof workspaces and inspects every theorem's axiom dependencies.

## Review the statements and their hypotheses

The source-level witness specification is
[`Source.ValidWithdrawal`](TornadoProofs/Witness/WithdrawalSource.lean): the
original 31-byte note components, public-field bounds, expected root, and the
actual 20-parent MiMC membership computation. It assumes neither witness
generation nor final R1CS or proof acceptance.

[`prepareInputPrefix_iff_source`](TornadoProofs/Witness/InputInverse.lean)
proves that the real input validator accepts exactly this domain and returns
the specified original input prefix. This includes every path direction and
the leaf-index bound.

[`referenceMeaning_construct`](TornadoProofs/Witness/ReferenceProgramMeaning.lean)
derives every point-operation domain and both original note hash identities
from those source facts and the authenticated public generators. The proof
uses the actual little-endian note bytes, all five native Pedersen segments,
complete Edwards addition, and the original successful public compilation.
It does not ask the caller to assume that the circuit calculation agrees
with native hashing or that a generated witness passes its checker.

[`native_construct_accepted_witness`](TornadoProofs/Witness/NativeWitnessConstruction.lean)
then proves that every input accepted by the original validator has a native
28,300-slot canonical witness, the exact six reviewed public signals, and all
28,275 authenticated R1CS equations. Witness generation and checker success
are conclusions. This is a useful completeness result for the witness stage;
it does not assert chain inclusion or successful withdrawal.

For proof-output privacy, read
[`native_original_worker_reference_bound`](TornadoProofs/Witness/NativeWorkerReference.lean).
It extracts actual input validation from the original worker's admission
prefix and constructs the witness evidence before applying
[`OutputSimulation.original_worker_reference_bound`](TornadoProofs/OutputSimulation.lean).
Key decoding, H construction and the context's setup/query/QAP relations
remain explicit; the wrapper does not synthesize an arbitrary honest setup
context from an asset digest.
For one admitted original source context, every terminal stdout/stderr/exit
status event differs from an explicit witness-free reference by at most
`2^-251`. The reference depends on the known request, public signals and
abstract setup trapdoor scalars, with no note, witness, H array or real witness
offsets. It is not an efficient public simulator or a trapdoor-recovery
algorithm. This statement does not require a second valid witness to exist.

[`WorkerPrefix.original_worker_output_privacy`](TornadoProofs/WorkerPrefix.lean)
compares two admitted contexts with the same setup and public signals. Both
results include the original sequential byte sampler, retry exhaustion,
actual native assembly, normalization, encoding, compiled-key acceptance,
request validation and fixed terminal failure, without conditioning on later
success. Privacy alone is not a release-probability guarantee: native verifier
completeness is a separate result with explicit finite-output conditions.

[`ProofPrivacy.Context`](TornadoProofs/ProofPrivacy.lean) and
[`PipelineComposition.ExecutionSource`](TornadoProofs/PipelineComposition.lean)
spell out the independent source/key/row assumptions. Read those structures,
not just the endpoint name. `QapSource.HSource` derives the actual H return and
QAP identity from original degree-bounded row equations. The witness modules
connect original primitive execution and public compilation to DAG meanings
and local circuit equations. The public certificate checker supplies the
full-circuit row implication without treating its untrusted extractor as a
mathematical oracle.

The full-program statement explicitly factors the original source into its
input-admission prefix and entropy/proof tail. It covers successful
note/request/public-asset admission. The actual file interpreter, physical
partial writes, elapsed time, CPU/memory access, process failures and OS
entropy distribution are separate trust boundaries. Malformed note parsing
and arbitrary hostile key material are not hidden by the same-public-input
privacy statement. No proof here authenticates RPC truth, Ethereum consensus,
the deployed contract, or the setup ceremony.

`GzipBackreference.appendMatch_same_state` proves exact state-and-error
preservation for the decoder's buffer ownership optimization. Runtime and
math-library code remain distinct: the theorem justifies the functional
change; it does not formalize allocator performance or the native compiler.
