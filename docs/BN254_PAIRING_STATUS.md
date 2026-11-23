# Native BN254 pairing and Classic verifier scope

The modules are imported by `Tornado.lean` and exercised by the repository's
verification gate. They validate public proofs in the isolated worker and
parent acceptance path used by experimental withdrawals. They do not themselves
sign, submit, authenticate chain state or prove deployed verifier identity.

## Implemented

- `BN254PairingField.lean`: canonical Fp6/Fp12 arithmetic for the Ethereum
  BN254 tower `v³ = 9 + i`, `w² = v`. It checks every returned inverse by
  multiplying back to one. Lean proves both inverse-success guards.
- `BN254TatePairing.lean`: a reference reduced Tate pairing using affine
  E(Fp12) lines, a full vertical denominator, an Fr Miller loop, a final
  exponent, on-curve checks, and an explicit G2 subgroup check. Lean proves
  successful results are nonzero and have Fr order. It is slow but native Lean.
- `BN254Groth16Verify.lean`: the Classic four-pair Groth16 verification
  equation with six bounded public signals and seven checked IC points.
  It returns `false` for a failed equation and errors for malformed inputs.
  Lean proves that every successful public-input commitment, and every direct
  `verify = .ok true` result, had signals below the scalar-field modulus.

## Evidence

- Three Fp6/Fp12 arithmetic vectors from pinned `@noble/curves@2.2.0`
  match exactly, including inverses and exponentiation.
- Three public generator reduced Tate output vectors from an independent
  noble-arithmetic implementation match exactly. The result is nontrivial,
  has Fr order, and is bilinear under doubling in G1 and G2.
- The archived Classic [Verifier.sol](https://github.com/tornadocash/tornado-core/blob/1ef6a263ac6a0e476d063fcb269a9df65a1bd56a/contracts/Verifier.sol)
  at commit `1ef6a263ac6a0e476d063fcb269a9df65a1bd56a` is vendored as a
  MIT-licensed offline test asset with SHA-256
  `a2fd9a12dc008ae95e1f9da2968e7d017617e804f22aa0491d2e8a91d965a824`.
  The provenance check parses and compares **all** alpha, beta, gamma, delta,
  and seven IC points against the JSON key fixture. Alpha, beta, and delta
  decoded independently from the pinned proving key also match.
- The pinned full public Groth16 proof is accepted by the native reduced Tate
  equation and by noble's optimal Ate pairing. Both reject a one-unit change
  at **each** of the six public-signal positions. All six native `vkX`
  coordinates also match noble. Native tests reject malformed/off-curve public
  points, a non-subgroup G2 point, bad IC length, and noncanonical signals.

## Boundaries

- The proofs of inverse, output, and signal-bound guards are kernel-checked and use no custom
  axioms. They do **not** prove extension-field laws, Miller-loop correctness,
  nondegeneracy, or Groth16 soundness. Differential tests cover public vectors.
- Reduced Tate outputs differ from EIP-197 optimal Ate bytes. For correctly
  implemented nondegenerate bilinear pairings on the same prime-order groups,
  the four-pair equality is equivalent; that correspondence is not proved
  in Lean here. The pinned proof test exercises the equality on real data.
- Arithmetic and subgroup checks are variable-time. This implementation is
  suitable only for public points and signals, never private witness scalars.
- Affine proof points and `vkX` at infinity are rejected. The production
  prover already rejects A/B/C infinity; the `vkX` case is conservatively
  rejected instead of emulating the EIP-197 identity case.
- The generic verifier accepts a caller-supplied key. The connected
  `ClassicVerifyingKey.verifyClassic` wrapper instead uses compiled, checked
  constants, compared offline with the archived source and proving key.
  These checks do not prove that the selected deployed pool uses that
  verifier or authenticate its runtime code on the selected chain.

## Reproduction

The source modules compile with Lean 4.29.1 and the repo's existing BN254
modules. From the repo root, run the three test files with `lake env lean
--run`. Run `scripts/generate-bn254-tower-vectors.mjs --check`,
`scripts/generate-bn254-tate-vectors.mjs --check`,
`scripts/check-tornado-proof-equation.mjs --check`, and
`scripts/check-classic-vk-provenance.mjs` for the offline independent oracle
checks. The first three need the sibling CLI's pinned noble package or
`NOBLE_BN254_JS` pointing to a noble `bn254.js`. Oracle scripts are
development-only; the Lean runtime has no C or JS pairing dependency.
