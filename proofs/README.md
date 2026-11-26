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
MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d proofs exe cache get \
  Mathlib.Algebra.BigOperators.Fin \
  Mathlib.Algebra.BigOperators.Group.Finset.Basic \
  Mathlib.Algebra.BigOperators.Group.List.Basic \
  Mathlib.Algebra.BigOperators.Intervals \
  Mathlib.Algebra.BigOperators.Ring.Finset \
  Mathlib.Algebra.Field.Basic \
  Mathlib.Algebra.Field.ZMod \
  Mathlib.Algebra.Group.Hom.Defs \
  Mathlib.Algebra.Polynomial.BigOperators \
  Mathlib.Algebra.Polynomial.Eval.Degree \
  Mathlib.Algebra.Polynomial.SpecificDegree \
  Mathlib.Algebra.QuadraticAlgebra.Basic \
  Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point \
  Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point \
  Mathlib.Data.Finset.Prod \
  Mathlib.Data.Fintype.BigOperators \
  Mathlib.Data.Fintype.Card \
  Mathlib.Data.Fintype.EquivFin \
  Mathlib.Data.Fintype.Prod \
  Mathlib.Data.Fintype.Sum \
  Mathlib.GroupTheory.OrderOfElement \
  Mathlib.Logic.Equiv.Basic \
  Mathlib.NumberTheory.LucasPrimality \
  Mathlib.RingTheory.AdjoinRoot \
  Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots \
  Mathlib.SetTheory.Cardinal.Finite \
  Mathlib.Tactic.Abel \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.LinearCombination \
  Mathlib.Tactic.NormNum \
  Mathlib.Tactic.NormNum.Prime \
  Mathlib.Tactic.ReduceModChar \
  Mathlib.Tactic.Ring
```

## Native arithmetic and proof construction

The theorem statements refer to the original `LeanCrypto` definitions, not
an independently executable replacement. Independent mathematical models
supply the specification; constructors derive actual native returns from
original-input conditions instead of assuming successful final checks.

- `Primes`, `CertifiedFields` and `BabyJubjub/Primes` certify the field and
  subgroup primes with explicit kernel-checked Lucas/Pratt certificates.
  `FpModel`, `FrModel`, `Fp2Model`, `Fp6Model` and `Fp12Model` relate native
  arithmetic, inverses and exponentiation to mathematical fields.
- `FFT/NativeTransform` proves complete native forward and normalized inverse
  DFT semantics and roundtrip at every admitted power-of-two length through
  65,536. `FFT/HConstruction` constructs sparse accumulation, transforms,
  convolution, high-half extraction and trimming, proves H fits the
  domain-minus-one query, and derives the QAP quotient equation from the
  independently specified constraint rows and polynomial degrees.
- The G1 and G2 group, scalar, normalization and MSM modules connect actual
  native addition, doubling, scalar loops and bucket algorithms to Mathlib
  elliptic-curve groups. Generator order uses unreduced native calculations;
  initially reducing the scalar would make that check vacuous.
- `AssemblySource`, `AssemblyGroup`, `AssemblyScalars` and `AssemblyFormula`
  construct the original Groth16 assembly and prove all A/B/C formulas.
  `NormalizationUniqueness`, `ProofCodec` and `ProofObservation` connect the
  actual point coordinates and exact eight-limb serializer, including its
  exceptional outcomes, to the mathematical scalar triple.
- The Tate function-field, native line and Miller modules derive actual
  evaluation, including denominator guards. `BilinearPairing` constructs the
  original public pairing return and proves additivity in both arguments.
  `VerifierCompleteness.assembly_qap_verifies` then constructs native verifier
  acceptance from original assembly and QAP equations, with explicit honest
  setup/query/verifying-key relations and the executable's finite-point
  conditions. Pairing or verifier acceptance is not a premise.
- `ConstraintCertificate` proves the pure checker for public linear
  elimination and R1CS row derivations. The application uses that checker
  on the full pinned circuit before reading a note or entropy.
- `BabyJubjub/Parameters` proves the actual Edwards coefficient a is a square
  and d a nonsquare, and derives complete addition denominators.
  `NativeWindows`, `WindowSeparation` and `TableSeparation` tie the native
  signed-nibble loop to bounded, nonzero scalars and prove table/prefix
  additions cannot collide or cancel modulo the certified subgroup order.

The setup relations are mathematical assumptions about the original encoded
key and ceremony. A digest authenticates bytes; it does not establish an
honest setup, the meaning of a point query, or a deployed verifier's identity.
Native Tate pairing is not formally identified with Ethereum's optimal Ate
precompile. Cryptographic soundness, discrete-log hardness, timing, resources
and secret erasure are not consequences of these algebraic results.

## Native proof-output distribution

`Groth16IdealPrivacy` proves exact observation counts for full-field masks
and the explicit nonzero-mask event bound `4q/(q−1)²`, retaining retry failure.
`Groth16SharedSamplerBridge` and `SamplerField` connect that statement to
bounded rejection sampling and canonical native scalar-to-field decoding.
The [application workspace](../app-proofs/README.md) connects the original
native assembly, acceptance, wire validator and worker terminal output to the
same observation, under its source and honest-setup conditions. The resulting
BN254 event bound is at most `2^-251`, under IID uniform 32-byte draws.
This is a statistical output statement for a fixed public setup and public
signals. It excludes time, memory, OS behavior and history-query linkage.

## Checking the evidence

Every named theorem has exactly one axiom inspection. The gate rejects custom
axioms and proof escapes and permits only standard `propext`,
`Classical.choice` and `Quot.sound`. Logical hypotheses remain in theorem
statements; an allowed axiom list does not mean a statement has no hypotheses.

This validation uses pinned Mathlib sources and official precompiled caches.
Project proofs are compiled and kernel-checked against those imported library
artifacts. The entire dependency tree is not rebuilt from source. Imported
library/build artifacts and the compiler remain trusted. See the
[parent specification](../docs/SECURITY_SPEC.md) for executable,
OS, setup, chain and side-channel boundaries.
