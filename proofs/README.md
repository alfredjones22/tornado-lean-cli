# Mathematical proofs

This proof-only Lake workspace uses Mathlib at immutable revision
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`, compatible with Lean 4.29.1.
Its manifest pins every transitive revision. The runnable `LeanCrypto` package
and CLI do not import this workspace or depend on Mathlib.

```sh
lake -d proofs build
node scripts/verify.mjs --kernel-only
```

On a fresh checkout, dependencies resolve from the pinned manifest. The
following targeted cache request covers the current direct Mathlib imports
and their dependencies, including the G1 Jacobian group bridge:

```sh
lake -d proofs exe cache get \
  Mathlib/Algebra/Field/Basic.lean Mathlib/Algebra/Field/ZMod.lean \
  Mathlib/Algebra/BigOperators/Fin.lean Mathlib/Algebra/BigOperators/Intervals.lean \
  Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean \
  Mathlib/Data/Finset/Prod.lean Mathlib/Data/Fintype/BigOperators.lean \
  Mathlib/Data/Fintype/Card.lean Mathlib/Data/Fintype/EquivFin.lean \
  Mathlib/Data/Fintype/Prod.lean Mathlib/Data/Fintype/Sum.lean \
  Mathlib/Logic/Equiv/Basic.lean Mathlib/NumberTheory/LucasPrimality.lean \
  Mathlib/SetTheory/Cardinal/Finite.lean Mathlib/Tactic/FieldSimp.lean \
  Mathlib/Tactic/Linarith.lean Mathlib/Tactic/NormNum.lean \
  Mathlib/Tactic/NormNum/Prime.lean Mathlib/Tactic/ReduceModChar.lean \
  Mathlib/Tactic/Ring.lean
```

## Native representation and construction

`Primes` contains explicit Lucas/Pratt certificates. Lean checks the products,
recursive prime facts and modular-power conditions; untrusted factor search
is not the certificate. `CertifiedFields` closes the actual base/scalar prime
hypotheses. `FpModel` and `FrModel` relate native modular operations and total
binary exponentiation to `ZMod`, and construct the actual checked inverse for
every nonzero modeled input.

`RootConstruction` constructs canonical roots of exact multiplicative order
for every admitted FFT length, the powers of two through 65,536.
`ButterflyModel` proves the actual indexed update's field meaning and
preservation properties. `TwoPointModel` proves the actual forward and
normalized inverse size-two DFT. General FFT/IFFT and H/QAP derivation are
not proved by these local results.

`JacobianModel` proves preservation of the admitted G1 representation,
including the native infinity sentinel. `G1GroupLaw` maps actual native
addition and doubling to Mathlib's established elliptic-curve group, covering
all branches. `JacobianNormalization` constructs actual normalization from a
nonzero Z and projective curve equation, and handles canonical infinity.
`NormalizationGroupLaw` connects those actual results to the same group sums.
Group equality here is after mapping representations, not raw-coordinate
identity. `ScalarMulGroupLaw` and `ScalarMulNormalization` prove that the actual total native scalar loop preserves
admission and represents `(n % q) • P`, where `q` is the BN254 scalar
prime, or `n • P` for canonical `n < q`.
It also constructs its normalized group result. G1 group/subgroup order and
removing the modulo restriction for arbitrary n remain open.

The windowed-MSM proof modules cover the actual private bucket/Horner engine,
its native G1 transport and the public entry point. `msmG1_success_sum` binds
public success to the exact ordered decoding of the original point array,
matching counts, canonical original scalars and the mathematical weighted sum.
`msmG1_success_normalized_sum` constructs the actual optional affine result
representing that same sum. G1 MSM correctness is therefore established on
accepted inputs; G2 MSM/group and full Groth16 point assembly remain unproved.

`ProofCodec` proves the actual private word loop constructs fixed-width
big-endian bytes and the public serializer yields 256 bytes with all eight
ordered limbs recoverable. `NormalizedProofCodec` discharges finite G1 A/C
normalization from independent curve conditions; G2 normalization output
remains an explicit premise. This does not prove the verifier's parser,
G2/pairing semantics or a map from ideal scalar triples to real proof bytes.

## Ideal observation counts and remaining privacy boundary

`Groth16IdealPrivacy` assumes a common public setup with nonzero δ and
compatible offsets `δK = AB − κ`. Bijective affine transport of full-field
masks preserves the ideal Groth16 triple and every common deterministic
observation's exact counts. With nonzero masks, the explicit event-probability
bound is `4q/(q−1)²`; the bounded model retains its common retry-failure outcome
without success conditioning.

`Groth16SharedSamplerBridge` identifies the shared sequential sampler's
weights and failure/success coefficients. `SamplerField` closes the stronger
canonical scalar-to-field bijection and arbitrary-event pushforward,
including actual full-width byte decoding and every bounded retry outcome.
The ideal event bound therefore applies to that field-cast observation of
the shared pure sampler under IID uniform input bytes.

This does not establish the distribution of the complete worker's released
bytes or additional failures. The application has constructive Num2Bits248
and DualMux gadget results; complete witness-gadget correspondence remains
open. General FFT/H/QAP, group/subgroup order, G2 MSM/group
and pairing correspondence and the factorization of actual coordinates,
encoding and release through the ideal triple remain unproved. OS/native
entropy-distribution coupling, timing, resources, erasure and history/RPC
privacy are outside these mathematical results. No implementation
zero-knowledge or end-to-end fund-safety claim follows.

This validation uses pinned Mathlib sources and its official precompiled
caches. Project proof source is compiled and kernel-checked against those
imported library artifacts; the entire dependency tree was not rebuilt from
source. Imported dependency/build artifacts and the compiler remain trusted.

Every named theorem has an axiom inspection. The verification gate rejects
custom axioms and proof escapes, and permits only standard `propext`,
`Classical.choice` and `Quot.sound` dependencies. Compiler/runtime, OS, honest
setup, chain and side-channel assumptions remain separately visible in the
[parent specification](../docs/WITHDRAWAL_SECURITY_SPEC.md).
