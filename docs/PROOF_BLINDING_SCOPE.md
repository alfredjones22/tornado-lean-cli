# Native Groth16 blinding scalar sampler

[`Tornado/Runtime/ProofBlinding.lean`](../Tornado/Runtime/ProofBlinding.lean)
samples `r` and `s` as nonzero canonical elements of the BN254 scalar field
`Fr`. Each candidate is a separate 32-byte read from
`Entropy.readKernelRandom`. A candidate is accepted only when
`1 <= value < Fr`; zero and values at or above `Fr` cause another fresh read.
There is **no modulo reduction**, so, assuming independent uniform kernel
bytes, the accepted scalar distribution has no modulo bias. Each scalar has
at most 512 attempts; exhaustion, malformed reads, and CSPRNG failures stop
with an error. Equal `r` and `s` values are possible by random coincidence;
the sampler never reuses a read for both.

`Scalar` carries proofs of positivity and field membership. The Lean theorem
`admitted_scalar_shape` proves that a successfully admitted candidate came
from exactly 32 bytes and is within the nonzero canonical `Fr` range.
The injected callback in `samplePairWith` supports deterministic offline
tests: `lake env lean --run tests/ProofBlinding.lean`.

## Conditional distribution proofs

The IO sampler, isolated worker and mathematical draw-tree interpretation
instantiate the same `sampleLoop` / `samplePairLoop`. The model also uses the
runtime candidate classifier after erasing the scalar's proof fields;
`runtime_candidate_matches` establishes that equality. This avoids a separate
retry algorithm used only for proofs.

Let `D = 2^256`, `q = Fr`, `a = q - 1`, `b = D - a`, and `n = 512`.
Assume each decoded entropy candidate is an independent uniform integer in
`[0,D)`. Finite tree counts use denominator `D^n` for a scalar and `D^(2n)`
for the sequential pair. Unused suffix coordinates contribute multiplicity;
the runtime does not read or preallocate them.

- [`BlindingDistribution`](../Tornado/Spec/BlindingDistribution.lean) derives
  each accepted value's equal count from the executed draw branches and
  proves normalization. The exhaustion count is exactly `b^n`; the sum of
  all successful counts plus that failure count is `D^n`.
- Conditional on sampler success, every nonzero canonical scalar has
  probability `1/(q-1)`. The successful denominator is proved positive for
  `q>1` and a positive draw budget. No uniform output weights are assumed.
- [`BlindingPair`](../Tornado/Spec/BlindingPair.lean) proves joint count
  factorization and conditional pair uniformity/independence. Its sequential
  continuation lemma handles the variable number of draws consumed by the
  first scalar; the next sampler uses the next unread independent coordinate.
- [`BlindingBounds`](../Tornado/Spec/BlindingBounds.lean) instantiates the
  actual modulus and 512-attempt limit. Exact integer inequalities prove
  scalar exhaustion probability at most `2^-128`, and failure of either
  sequential scalar at most `2^-127`. These conservative bounds exclude OS
  read failures and all later prover failures.

The conditional statements use cross-multiplied integer counts, with positive
denominator theorems, rather than floating-point estimates. Their proof
dependencies are inspected by `#print axioms` in the verification gate.
They do **not** prove kernel entropy, byte-decoder distribution equivalence,
independence of OS reads, or the behavior of a substituted entropy source.
Those are the explicit decoded-candidate entropy contract.

Nor do they prove secrecy of Groth16 proof construction, absence of information
encoded into proof bytes, or independence after conditioning on a later
witness/prover/transport failure. They are distribution results for the
sampler's success, not a zero-knowledge theorem for the complete CLI.

The connected experimental worker uses this sampler for fresh proof blinding.
The current native prover still uses variable-time bigint and elliptic-curve arithmetic, and
neither entropy buffers nor secret-bearing intermediates are zeroized. Those
properties can leak information through timing or retained process memory.
Adding this sampler alone does not make native proof generation safe for
private notes or production withdrawals.
