# Native Tornado witness execution

[`WitnessVM.lean`](../Tornado/Protocol/WitnessVM.lean) evaluates all **36,528
signals** and materializes all **28,300 R1CS variables** of the pinned Classic
Tornado `Withdraw(20)` circuit in native Lean. It does not execute JavaScript,
call the TypeScript CLI, or copy witness values from the test fixture. It takes
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

This does not prove every other instantiated template, all original constraint
rows or global witness construction for every valid input. Other graph/primitive
correspondence remains tested rather than fully proved. The separate BN254
G1/MSM results do not prove the BabyJub/Pedersen or MiMC witness gadgets. See
[proof scope](PROOF_SCOPE.md) and the [mathematical workspace](../proofs/README.md).
The pinned circuit itself, proving key, deployed verifier, and consensus chain
are external trust boundaries. A satisfying witness does **not** produce a
Groth16 proof, establish that a note is unspent, or validate the pool root.

The field and point operations are variable-time and do not zeroize
note secrets. Connected experimental withdrawals have no production
side-channel or secret-erasure guarantee.
Full proving, including MSM, blinding, pairings and proof serialization, is
implemented in separate modules. Development uses only public unfunded fixtures.
