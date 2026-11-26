# Native BN254 Fr FFT scope

[`FrFFT.lean`](../Tornado/Protocol/FrFFT.lean) implements the radix-two
number-theoretic transform needed by the pinned Tornado Groth16 prover. It
uses the BN254 scalar field, NQR **7**, and supports power-of-two arrays up to
65,536 values (twice the 32,768-row proving domain). The root calculator
checks that the chosen root has the requested exact power-of-two order, and
inversion checks its multiplicative result. The separate
[mathematical workspace](../proofs/README.md) certifies the scalar prime and
constructs the actual inverse for every nonzero modeled input. It constructs
canonical roots of exact multiplicative order for every admitted size, and
proves the actual indexed butterfly, complete forward and normalized inverse
DFT, bit-reversal and stage loops, and FFT/IFFT roundtrip for every admitted
length. These are universal source-level constructions, rather than
assumptions that the native transform returned successfully. See
[`NativeTransform.lean`](../proofs/LeanCryptoProofs/FFT/NativeTransform.lean).

The pinned reference SDK's `createTornadoProver` passes `nqr: 7` into
`micro-zk-proofs@0.3.1`; that library uses `@noble/curves`' BN254 Fr FFT. The
SDK's old proving key was built using websnark's NQR 7. Using another
nonquadratic residue changes the root tower and yields a different H
polynomial. The native code implements a natural-order radix-two DIT FFT and
inverse independently of the JavaScript library.

`calculateH` takes witness values and sparse signal-indexed A/B polynomials,
builds the domain evaluation vectors, inverse-transforms them, convolves the
coefficient vectors on the 65,536-point domain, and returns the upper half of
the product after trimming trailing zero coefficients. The old binary key
stores A and B, not C. C has degree below 32,768, so subtracting it cannot
alter the upper half. This matches the H path used by
`micro-zk-proofs.calculateH` for the pinned key.

[`fr-fft-vectors.json`](../fixtures/fr-fft-vectors.json) contains seven finite
FFT/IFFT cases (sizes 1 to 64), one 32,768-point sparse-input spot vector,
three sparse-H cases (domains 4, 8, 16), the
32,768- and 65,536-point roots, and the inverse of 32,768. The development
extractor [`generate-fr-fft-vectors.mjs`](../scripts/generate-fr-fft-vectors.mjs)
recomputes the fixture against the pinned noble implementation. Its H cases
also check the result against naive coefficient convolution. The Lean test
[`FrFFT.lean`](../tests/FrFFT.lean) compares the native outputs, checks a
full 32,768-point inverse roundtrip, and rejects
non-power-of-two lengths, out-of-field inputs, invalid roots, and zero
inverse requests. These are finite compatibility tests, not a universal proof.

`calculateH` is a pure building block; it accepts ordinary arrays and does not
carry the proving key's digest proof itself. The complete proof pipeline obtains
its polynomials through `authenticatePinnedKey` and `decodeFullKey`, checks the
complete witness, and records that the same witness and decoded key supplied
the native H calculation.

[`HConstruction.lean`](../proofs/LeanCryptoProofs/FFT/HConstruction.lean) proves
the actual sparse accumulation, inverse transforms, convolution, high-half
extraction and trailing-zero trimming construct H. Its stronger dimension
result is `h.size ≤ domain − 1`, matching the setup query length. From
independent degree-bounded A/B/C polynomials, original sparse-row alignment
and satisfied row equations, `calculateH_quotient` derives
`H(X)·(X^domain−1) = A(X)·B(X)−C(X)`. A quotient or successful verifier result
is not a premise.

The application
[`HSource`](../app-proofs/TornadoProofs/QapSource.lean) makes those source
conditions explicit. The offline `check-qap-alignment.mjs` additionally checks
every stored A/B coefficient against the pinned R1CS, seven public unit rows,
and zero padding. That finite artifact check is not a kernel proof of the
binary parser or of an honest setup. See
[pipeline scope](CLASSIC_PROOF_PIPELINE_SCOPE.md). This code
is variable-time bigint arithmetic, used by the isolated experimental worker
with no constant-time or erasure guarantee and no side-channel certification.
Groth16 MSMs, blinding, pairing verification and withdrawal
orchestration are implemented in separate modules, not in this FFT component.
