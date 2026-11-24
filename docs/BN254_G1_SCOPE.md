# Native BN254 G1 arithmetic scope

[`BN254G1.lean`](../Tornado/Protocol/BN254G1.lean) implements the BN254 base field and G1 curve arithmetic in native Lean: bounded field values, modular add/subtract/multiply, checked inversion, affine on-curve validation, Jacobian add/double, scalar multiplication, and affine normalization. It uses the exact base-field and scalar-field parameters in the pinned `@noble/curves` package. No external crypto library is called by the Lean implementation.

[`tests/BN254G1.lean`](../tests/BN254G1.lean) checks 14 public scalar/addition outputs against [pinned noble vectors](../fixtures/bn254-g1-vectors.json), plus off-curve, out-of-field, and zero-inverse rejection. [`generate-bn254-g1-vectors.mjs`](../scripts/generate-bn254-g1-vectors.mjs) regenerates those vectors from the local pinned TypeScript dependency; `--check` compares them byte for byte. The separate [mathematical workspace](../proofs/README.md) goes beyond these
vectors: certified prime facts close native Fp inverse construction, and admitted
G1 representations map actual add/double to Mathlib's elliptic-curve group.
Actual normalization constructs the same group point. The total scalar loop
represents `(n % q) • P`, or `n • P` for canonical `n < q`; this does not prove
G1 group/subgroup order. The actual windowed G1 MSM also has original ordered
point/scalar weighted-sum and normalization theorems. G2 and full Groth16
correspondence remain separate; see [proof scope](PROOF_SCOPE.md).

This module is an arithmetic building block used by the isolated Lean prover. Its direct vectors use public points; worker integration uses public unfunded proof fixtures. Arithmetic is variable-time and does not zeroize secrets. Secret erasure and side-channel safety are outside current verification coverage, including for experimental live commands.
