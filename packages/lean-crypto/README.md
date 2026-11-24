# LeanCrypto

A pure Lean library extracted from the native cryptographic implementations in
the parent project. The package has one Lean library, `LeanCrypto`, and depends
only on the pinned Lean toolchain. It imports no application, CLI, RPC, native
signer, filesystem, entropy source, circuit asset, or proving-key package.

Use the umbrella import or import the modules needed by a consumer:

```lean
import LeanCrypto.Keccak
import LeanCrypto.BIP32
import LeanCrypto.FixedBytes

open LeanCrypto

#check keccak256
#check bip32HardenedPath
#check FixedBytes.decode_encode
```

A local Lake consumer can declare `require leanCrypto from "../lean-crypto"`.
The extraction's separate compatibility consumer checks that legacy qualified
names alias the same canonical types, constructors, projections, functions, and
theorem terms. Application-specific mnemonic paths and signature-note envelopes
remain in the parent application.

## Modules

- `Keccak`, `SHA256`, `SHA512`, and `Blake256`: Keccak-256 with Ethereum's 0x01
  domain, SHA-256/512, HMAC, and legacy BLAKE-256.
- `MiMC`, `MiMCTree`, and `Pedersen`: the existing 220-round MiMC sponge,
  retained Merkle zero-leaf/20-level defaults, and BabyJubJub Pedersen encoding.
  These compatibility parameters are explicit parts of their current APIs.
- `BIP39`, `BIP39Words`, and `BIP32`: English mnemonic checks and PBKDF2 plus
  hardened private derivation. Unicode BIP39 passphrases requiring NFKD and
  non-hardened child derivation are outside the implementation's scope.
- `Secp256k1`: public keys, Ethereum address bytes, and deterministic low-S
  RFC6979 signing. `Constants` provides its order directly, so importing this
  module does not import BIP32, BIP39, or a wordlist.
- `FixedBytes`, `Hex` and `HexWord`: fixed-width big-endian bytes and lowercase hex with
  checked construction/inversion laws. The width-preserving byte encoding keeps
  leading zeros. Hex decoding executes a proved tail-recursive implementation.
- `Sampling`: pure bounded retry loops, sequential pair sampling, and exact
  nonzero BN254 scalar admission. Consumers supply the effect and randomness.
- `Probability.Rejection`, `Probability.Pair`, `Probability.Bounds` and
  `Probability.ByteEntropy`: exact finite scalar/pair event counts, decoder
  bijections, retry exhaustion and conditional uniformity. The source model
  assumes independent uniform bytes; no OS randomness claim follows.
- `BN254.*` and `Groth16.*`: field/group/pairing and generic circuit/proof
  arithmetic contributed by the companion extraction. Public inputs and query
  arrays belong to the caller. Application-specific verifying keys, witness
  generation, circuit assets, pool rules, and six-signal withdrawal profiles
  stay in the parent application.

## Validation and limits

```sh
lake build standalone_consumer
.lake/build/bin/standalone_consumer
lake env lean --run tests/KeccakTests.lean
lake env lean --run tests/BIP32Tests.lean
```

The ten hash/key/curve compatibility suites contain 139 pinned checks, including
hash block boundaries, Merkle paths, malformed inputs, and deterministic signing.
Additional BN254 and generic Groth16 tests include a separate one-public-input
square circuit and changed-input rejection. These are executable compatibility
checks, not complete proofs of the cryptographic algorithms or their security.

The separate [proof-only workspace](../../proofs/README.md) uses pinned Mathlib
to relate selected actual native functions to fields, roots, a two-point DFT,
the G1 elliptic-curve group, constructive normalization and the eight-limb
Solidity byte codec. The actual windowed G1 MSM has original-input weighted-sum
and normalization theorems. The workspace also proves arbitrary-event sampler-to-field transport
and an ideal observation bound. The production package still has no Mathlib
dependency. Complete witness-gadget correspondence, group/subgroup order,
general FFT/H/QAP, G2 MSM/group/pairing and
the complete worker's observation distribution remain outside those results.

The byte/hex/sampling/counting theorems are kernel checked. Every theorem lists
its axioms, limited to Lean's standard axioms. There are no custom axioms,
`sorry`, `admit`, `native_decide`, unsafe declarations, or foreign primitives in
the production package.

Secret-dependent arithmetic is variable time, and ordinary Lean values and
runtime buffers provide no guaranteed zeroization. The package does not certify
constant-time execution, side-channel resistance, secure signing custody,
discrete-log assumptions, proof-system soundness, or production readiness.

## License

The extracted code retains the parent project's MIT license and copyright in
`LICENSE`. The frozen English wordlist came from the existing application copy
of the `@scure/bip39` distribution; its upstream MIT notice is retained in
`LICENSE-scure-bip39`. No UNLICENSED contract source or artifact is included.
