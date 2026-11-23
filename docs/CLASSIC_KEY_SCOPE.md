# Compiled Classic Groth16 verification key

[`ClassicVerifyingKey.lean`](../Tornado/Protocol/ClassicVerifyingKey.lean)
contains all Classic withdrawal verifier alpha, beta, gamma, delta, and seven
IC coordinates as decimal Lean literals. `checkedKey` rejects any noncanonical
field coordinate or off-curve/off-twist point before returning a key.
`verifyClassic` accepts only a proof and six public signals; it has no caller
supplied key parameter.

The coordinates come from the vendored, immutable [Tornado Core
Verifier.sol](../fixtures/tornado-classic-Verifier.sol) at commit
`1ef6a263ac6a0e476d063fcb269a9df65a1bd56a` (source SHA-256
`a2fd9a12dc008ae95e1f9da2968e7d017617e804f22aa0491d2e8a91d965a824`).
The offline `check-classic-vk-provenance.mjs` script compares the complete JSON
fixture to that Solidity source and compares alpha, beta, and delta to the
authenticated proving key. The dedicated Lean test compares every compiled
coordinate to the pinned JSON fixture, confirms seven IC points, and checks
noncanonical/missing-signal rejection. The resulting correspondence is finite
test and source-review evidence, not a Lean theorem about an external file.

Two kernel-checked Lean theorems constrain the native wrapper: any successful
`verifyClassic` result used `checkedKey`, and any accepted proof had canonical
Fr public signals. Neither theorem proves pairing arithmetic, Groth16
soundness, circuit semantics, or that this source key matches a particular
deployed pool's verifier. Deployed pool/verifier identity remains an external
assumption for connected experimental withdrawals; authenticated deployed-code
binding is not implemented. The pairing implementation
checks public proofs in the worker and parent acceptance path. Its arithmetic
correctness is not established by these wrapper theorems.
