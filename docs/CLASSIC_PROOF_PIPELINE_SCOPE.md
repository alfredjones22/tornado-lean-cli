# Native Classic proof pipeline scope

[`ClassicProofPipeline.lean`](../Tornado/Protocol/ClassicProofPipeline.lean)
composes native Lean withdrawal components into a checked proof route. The
isolated worker invokes this pipeline for explicitly experimental live
commands. Development proof runs use public, unfunded fixtures only. This
connection does not provide constant-time computation or secure secret erasure.

## Executable route

`loadBundled` authenticates the complete extracted witness graph and the
exact bundled compressed circuit and proving key. It decompresses both assets
with native Lean gzip, checks their compressed and raw SHA-256 digests, parses
the full R1CS, checks its 28,275 constraints against the pinned canonical
digest, and returns the private-constructor pinned graph, circuit, and key
values. A wrong graph digest fails before decompression. The fourth asset is
a bounded public witness derivation certificate. Before reading a note or
entropy, the worker checks it against every pinned R1CS row, binds circuit
bases to actual native generator/subgroup receipts and validates the complete
independent signed-window point schedule. The certificate extractor is
untrusted and no expanded DAG/transcript is retained for secret computation.

`prove` takes those authenticated assets, a native `WithdrawalInput`, and
explicit nonzero canonical Fr blinding scalars. It checks the note commitment,
nullifier hash, Merkle path, expected root, recipient, relayer, fee, refund,
and the 49-slot input prefix; generates the complete 28,300-slot witness in
Lean; checks every R1CS row; decodes the pinned proving key; derives H with the
native NQR-7 FFT; assembles A/B/C with native BN254 MSM; serializes the eight
Classic Solidity words; and verifies the exact same points with the compiled
Classic key and native reduced Tate pairing equation. A false equation or
malformed point is an error, not a returned proof.

The returned `PublicProof` contains only serialized bytes, public signals, and
the six reviewed public values. Its certificate is a proposition, erased from
compiled output. It existentially records a `CheckedArtifact` whose private
constructor carries kernel-visible equalities for the checked witness,
serialized bytes, derived verifier points, successful compiled-key pairing
equation, and public signals. `prove_success_from_original` and
`prove_success_assembled_and_serialized` additionally bind public success to
the original assets, withdrawal input and supplied `r,s`, through the actual
input prefix, witness generator, key decoder, H calculation, point assembly
and exact returned bytes. This is execution provenance, not a claim that every
valid input succeeds. The separate source construction, FFT/H/QAP, assembly
and native verifier theorems establish their stronger conditional mathematical
claims; see [proof scope](PROOF_SCOPE.md). Their
axiom reports contain only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. Neither the input note nor the checked witness is a runtime field
of the public result. The computation still holds secret intermediates in
memory while running and does not zeroize them.

The witness source predicate now characterizes actual successful input
validation in both directions. Its Pedersen bridge derives all point-operation
domains and exact original commitment/nullifier identities from the native
note bytes and checked public bases. This removes a caller-supplied
native-to-circuit agreement premise from witness construction. Key decoding,
row alignment, honest setup and finite-point conditions for the later proof
stages remain explicit boundaries.

## Validation

`classic_proof_pipeline_full_test` uses the public, unfunded
`abandon`/`art` note fixture with fixed `r=1,s=2`. It authenticates and
decodes the bundled gzip files, compares all six public signals and the exact
256-byte Solidity proof with the pinned SDK fixture, and requires the compiled
Classic verifier to accept it. The accompanying theorem certifies that the
complete 28,300-slot witness passed all 28,275 R1CS constraints. The separate
`groth16_full_public_test` compares that full witness with the pinned SDK fixture.
This pipeline test also checks wrong graph digest, zero/out-of-field blinding,
and wrong expected Merkle root. The public-certificate test independently
checks size/integrity/topology, native base bindings and 15 schedule cases,
including 13 adversarial structural mutations. Current timings and exact source
hashes belong to the generated verification report, not to a portability claim.

## Trust and production limits

- The separate [proof workspaces](../proofs/README.md) prove actual source
  arithmetic, complete transforms, both groups/MSMs, assembly, native pairing
  bilinearity/nondegeneracy and conditional verifier correctness. The
  application constructs witness execution and every row from explicit
  original-input conditions. A digest does not establish honest setup/query
  relations, and SHA/DEFLATE correctness/security, generic Circom/JavaScript
  translation and deployed EIP-197 implementation correspondence are separate
  boundaries. The full fixture remains finite evidence.
- The native `Nat`/big-integer, elliptic-curve, FFT, and pairing operations are
  variable-time and do not zeroize secret material. The API accepts explicit
  `r,s`; it does not securely sample fresh blinding scalars. Fixed fixture
  values are never suitable for funded notes. The worker samples fresh blinding,
  but its variable-time/nonzeroizing computation has no production
  secret-safety or side-channel guarantee.
- The root and Merkle path are caller supplied. The component does not verify
  chain state, note unspentness, selected pool/chain identity, fee funding,
  transaction destination, bundler/paymaster behavior, or deployed verifier
  code. The compiled Classic key is pinned to vendored source, but the selected
  pool's actual verifier remains an external trust boundary.
- This route holds decoded circuit, proving key, witness and FFT arrays in
  memory. It is slow and has not been resource-profiled for constrained
  devices. It does not write a durable attempt journal or send a transaction.
