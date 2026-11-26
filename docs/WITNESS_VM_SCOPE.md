# Native Tornado witness execution

[`WitnessVM.lean`](../Tornado/Protocol/WitnessVM.lean) evaluates all **36,528
signals** and materializes all **28,300 R1CS variables** of the pinned Classic
Tornado `Withdraw(20)` circuit in native Lean. Runtime witness generation
neither executes external scripts nor copies witness values from a fixture. It takes
the existing checked 49-slot input prefix, a native note commitment, and a
typed arithmetic graph. It executes the two `Num2Bits(248)` components, five
Pedersen segments, 2,234 typed point/mux/square operations, 20 Merkle
selectors, and all rounds in 40 `MiMCFeistel(220)` components. Wiring-only
templates are represented by shared signal indices. A signal can be written
twice only with an identical value; an unassigned signal is represented by
`none` and cannot be silently filled with zero.

The graph is extracted from the exact, SHA-256-pinned Circom JSON asset by
[`witness-vm-extract.mjs`](../scripts/witness-vm-extract.mjs). That development
script checks component types, aliases, base points, and topologically sorts
the primitive operations; `--check` regenerates and compares the checked-in
[`graph`](../fixtures/witness-vm-selected-components.json) byte for byte. The
native `decodePinnedGraph` checks the graph file's full SHA-256 and returns a
`PinnedGraph` with a private constructor and kernel-visible provenance proof.
The final witness API requires this certified graph. The script is a
reproducibility oracle, not a runtime dependency.

[`tests/WitnessVM.lean`](../tests/WitnessVM.lean) derives a public fixed note
using native Lean, computes its full witness, compares **every one of 28,300
R1CS slots** with the pinned SDK witness, and checks all **28,275** original
Tornado constraints. It also builds a two-leaf Merkle tree with the note at
index one and checks a second, independently generated full witness against
all 28,275 constraints. A third case derives different note material and uses
nonzero recipient, relayer, and fee values through `generateCheckedWitness`.
The fourth case places the note at the rightmost leaf of a full-depth
synthetic tree, exercising the right-hand branch of all 20 Merkle selectors.
Every one of the 36,528 signal assignments is present in all four cases.
Invalid mapping bytes, conflicting signal assignments, wrong
roots, non-bit selectors, and oversized bit inputs are rejected.

`authenticatePinnedCircuit` checks the decoded circuit's canonical SHA-256
against the exact pinned R1CS and returns a `PinnedCircuit` with a private
constructor and kernel-visible dimension/digest proofs. The development
extractor computes the same digest from the SHA-256-pinned circuit asset.
`generateCheckedWitness` accepts both certified values, requires **all 36,528
internal signal assignments**, and checks every equation before returning a
native witness. A missing internal signal above the R1CS variable range is
rejected by `toWitness` and the final API. A single
authenticated circuit can be reused across withdrawals without rehashing its
7.6 MB canonical encoding each time. The isolated worker invokes this function
through the Classic proof pipeline for experimental withdrawals. Parent commands
join public history checks, protected reservations and proof acceptance; these
components do not authenticate Ethereum consensus state.

## Proof and trust limits

The guard theorems show that every witness accepted by the final native API
passed the complete R1CS checker. `Spec/WitnessGadgets.lean` additionally
constructs the actual Num2Bits248 and DualMux assignments from independently
supplied original inputs, slot bounds and compatible aliases. It proves the
stored boolean/reconstruction/mux equations and assignment preservation, with
no final-R1CS-success premise. The extracted selector refactor is proved equal
to the entire original Merkle-level implementation, including errors.

The application proof workspace now covers all primitive kinds, Num2Bits,
public seeds, complete MiMC phases, every local row and original ordered
witness materialization. `CanonicalSource.generateCheckedWitness_source`
constructs the actual generation return from independently interpreted original
inputs and explicit arithmetic source conditions; it does not assume that
execution or the final R1CS checker succeeded.

Those arithmetic source conditions are now derived from the independent
`Source.ValidWithdrawal` predicate and the checked public bases in
`ReferenceProgramMeaning.referenceMeaning_construct`. The proof follows the
actual original note bits through all five signed-window segments and
complete Edwards additions, including the exact 31-byte concatenation and
25-byte chunk boundaries. It constructs the point-operation domains and
identifies the actual commitment and nullifier coordinates with native
Pedersen hashing. `InputInverse.prepareInputPrefix_iff_source` proves the
original input validator accepts exactly this source domain; it is not an
assumed replacement validator.

`NativeWitnessConstruction.native_construct_accepted_witness` composes that
source meaning with the actual public certificate and witness execution.
For every original accepted prefix, it constructs a canonical 28,300-slot
witness, its exact six reviewed public signals and all 28,275 checked R1CS
equations. None of those final checks is a premise of the theorem.

The public asset gate regenerates local equations, verifies their full linear
elimination against the actual pinned constraints, checks native generator
subgroup receipts and circuit-base binding, and validates an independent
signed-window point schedule. The BabyJubJub proofs connect actual native
addition, scalar multiplication and normalization to Mathlib's group, with
signed-window bounds and denominator conditions stated separately. The source
construction and reference program identify which original-input properties
are required; see [application proofs](../app-proofs/README.md).

These are statements about the pinned typed program and R1CS, not a general
Circom/JavaScript compiler equivalence theorem or a proof that the circuit
expresses every user expectation. Setup honesty, deployed code and consensus
state remain external. R1CS satisfaction does not establish unspentness or a
pool's acceptance of the supplied root. Full proof assembly and conditional
native verification have their own results in [proof scope](PROOF_SCOPE.md).

The field and point operations are variable-time and do not zeroize
note secrets. Connected experimental withdrawals have no production
side-channel or secret-erasure guarantee.
Full proving, including MSM, blinding, pairings and proof serialization, is
implemented in separate modules. Development uses only public unfunded fixtures.
