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
from exactly 32 bytes and is within the nonzero canonical `Fr` range. It
does **not** prove that the kernel bytes are random or independent. The
injected callback in `samplePairWith` supports deterministic offline tests:
`lake env lean --run tests/ProofBlinding.lean`.

The connected experimental worker uses this sampler for fresh proof blinding.
The current native prover still uses variable-time bigint and elliptic-curve arithmetic, and
neither entropy buffers nor secret-bearing intermediates are zeroized. Those
properties can leak information through timing or retained process memory.
Adding this sampler alone does not make native proof generation safe for
private notes or production withdrawals.
