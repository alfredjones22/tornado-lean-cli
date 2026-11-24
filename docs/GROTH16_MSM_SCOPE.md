# Native Groth16 point assembly scope

[`Groth16MSM.lean`](../Tornado/Protocol/Groth16MSM.lean) implements checked
BN254 G1 and G2 windowed bucket multi-scalar sums and the point formula used by the pinned
`micro-zk-proofs@0.3.1` Groth16 prover. The formula builds `pi_a` from the A
query, alpha, and `r·delta`; `pi_b` from the G2 B query, beta, and `s·delta`;
and `pi_c` from the private C query, H exponents, blinded A and G1 B sums,
and `−r·s·delta`. The C query begins after `nPublic + 1` witness slots,
matching the binary key's omitted public-signal identity points. The returned
public signals are exactly the witness slots after the constant-one slot.

The generic `assemble` entry point checks query sizes, the constant-one
witness slot, all Fr scalar bounds, C offset, and H length. Each MSM checks
point/scalar count and scalar bounds, and decodes even points whose scalar is
zero. [`groth16-msm-vectors.json`](../fixtures/groth16-msm-vectors.json) has
four public MSM vectors, three windowed cases (including 2,050 G1 points),
and one synthetic point-assembly vector calculated
independently using the pinned noble BN254 package. The
[`Groth16MSM.lean` test](../tests/Groth16MSM.lean) checks those values and thirteen
rejection cases. The extractor's `--check` mode reproduces the fixture.

The [mathematical workspace](../proofs/README.md) proves the actual bucket
fill, collapse and Horner/window algorithms for both G1 and G2, transports
them to Mathlib elliptic-curve groups, and constructs their native
normalizations. The exact generator orders are derived from unreduced
subgroup calculations and certified prime orders; reducing the scalar first
is not used as an order certificate.

[`AssemblySource`](../proofs/LeanCryptoProofs/AssemblySource.lean) constructs
the original `assemble` return from independently valid ordered key points,
matching dimensions and canonical scalars.
[`AssemblyFormula`](../proofs/LeanCryptoProofs/AssemblyFormula.lean) and
[`AssemblyScalars`](../proofs/LeanCryptoProofs/AssemblyScalars.lean) prove the
complete A/B/C formulas, including private C offsets, H prefixes and the
negative-rs term. Their `KeySpan` assumption states the mathematical meaning
of the actual key points.

`solidityProofBytes` normalizes the three proof points, rejects infinity,
and emits the Classic verifier's exact 256-byte order: A x/y; B x.c1/x.c0,
y.c1/y.c0; C x/y. A pinned SDK-shaped synthetic proof vector checks every
output byte and three of the rejection cases. `ProofCodec` also proves the
actual private word loop's fixed-width construction, 256-byte length and
recovery of all eight ordered limbs. `NormalizedProofCodec` discharges finite
G1 A/C normalization from curve conditions. The corresponding G2 construction
and representation uniqueness now discharge G2 normalization as well.
[`ProofObservation`](../proofs/LeanCryptoProofs/ProofObservation.lean) proves
that the actual coordinates and exact serializer result, including failures,
factor through the three mathematical group scalars.

`deriveCheckedProofPoints` is the pure authenticated-artifact route: it takes
the private-constructor pinned graph, circuit, and key types, generates and
checks the full native witness, parses the authenticated full key, computes H
with the native NQR-7 FFT, and assembles proof points from explicit `r` and
`s` blinding values. Its return type carries a kernel-visible proof that the
same returned witness passed all 28,275 native R1CS equations. Original-input provenance theorems trace a successful result through that
same witness generator, decoded key, H calculation and actual assembly.
The actual FFT/H, both curve groups, complete assembly and bilinear pairing
results are connected by
[`assembly_qap_verifies`](../proofs/LeanCryptoProofs/VerifierCompleteness.lean).
It constructs native verifier acceptance from the honest setup/query/key
relations and the QAP equation, without assuming successful pairing or
verification. Finite A/B/C and a nonzero public-input commitment are explicit
conditions because the executable rejects infinity. This is conditional
completeness, not cryptographic soundness, deployed-verifier equivalence or
proof that a hash-pinned setup is honest. See [proof scope](PROOF_SCOPE.md).

The compiled full 28,300-signal public test in
[`Groth16MSMFull.lean`](../tests/Groth16MSMFull.lean) authenticates the pinned
key, graph, and R1CS, checks all 28,275 constraints, computes H, assembles
the proof, and checks the exact 256 serialized bytes and SHA-256 against
[`groth16-full-public-proof.json`](../fixtures/groth16-full-public-proof.json).
That fixture comes from the independent
[`generate-full-public-proof.mjs`](../scripts/generate-full-public-proof.mjs)
oracle: sibling `tornado-cli-new-era` commit
`daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7`, pinned
`micro-zk-proofs@0.3.1`, noble BN254 v2.2.0, the authenticated public key,
and the pinned public witness. The oracle runs the SDK's `createProof` using
fixed test blinding scalars `r=1`, `s=2`. Its `--check` mode regenerates and
compares the fixture. These are deliberately public test values, not secure
production blinding.

On an Apple Silicon host, the native compiled test passed in 77.37 seconds
wall time (75.30 seconds user CPU, 158,105,600 bytes peak resident memory);
the Lean-reported route time was 75,605 ms. The independently pinned SDK
oracle also produced identical bytes, whose SHA-256 is
`db2b44928c30a739ce3a26191db4d83698277b758f642751d8e9a083f9fa78db`.
This establishes exact output parity for one public full-size fixture, not
general Groth16 correctness or deployed-verifier acceptance. MSM uses
windowed buckets with 4, 6, or 10-bit windows based on point count.

The arithmetic is variable-time and does not zeroize secrets. The connected
experimental worker samples fresh blinding from kernel entropy, authenticates
assets, checks the witness and verifies the serialized public proof. Parent
adapters bind reviewed inputs and revalidate known roots and spent status.
Those checks do not prove side-channel safety, trusted-setup
soundness or deployed verifier identity. Development uses public unfunded
fixtures only. Production secret safety and deployed-code authentication are
not established.
