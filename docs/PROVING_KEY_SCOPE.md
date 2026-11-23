# Native proving-key decoding scope

[`ProvingKey.lean`](../Tornado/Protocol/ProvingKey.lean) adds native Lean
decoding for every section of the pinned Tornado binary Groth16 proving key.
The existing [`Groth16Key.lean`](../Tornado/Protocol/Groth16Key.lean) checks
its 40-byte header and the exact section offsets. The SDK's legacy format
stores 32-byte little-endian Montgomery residues. This parser converts them
to canonical BN254 Fp coordinates or Fr coefficients, rejects truncated and
noncanonical values, checks G1 points against `y² = x³ + 3`, checks G2 points
against the BN254 twist using [`BN254G2.lean`](../Tornado/Protocol/BN254G2.lean),
maps the old G1/G2 sentinels to the group identity, and rejects duplicate or
out-of-domain polynomial row indices. Four kernel-checked theorems establish
that the pinned Montgomery inverse constants multiply `2^256` to one in Fp and
Fr and that an authenticated key carries the expected digest and validated
header. The inverse proofs use no axioms; the wrapper proofs use only Lean's
standard axioms.

`authenticatePinnedKey` SHA-256-checks the complete 14,522,256-byte
decompressed asset, validates its header, and returns a `PinnedKey` with a
private constructor and kernel-visible digest/layout proofs. `decodeFullKey`
accepts only that value. It parses five verifier-key points, **28,300 A** and
**28,300 B** sparse-polynomial records, **28,300 A-query G1** points,
**28,300 B1-query G1** points, **28,300 B2-query G2** points, **28,293
C-query G1** points, and **32,767 H-exponent G1** points. Each section must
consume exactly its pinned byte range. As in the SDK, the binary C-query
section omits the seven public-signal identity placeholders, which proof
assembly must prepend later.

[`proving-key-extract.mjs`](../scripts/proving-key-extract.mjs) checks the
decompressed asset's SHA-256
`8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af`
and deterministically extracts 12 G1, five G2, and eight A/B polynomial vectors into
[`proving-key-vectors.json`](../fixtures/proving-key-vectors.json). Its `--check`
mode regenerates and compares that small fixture byte for byte. The native
[`ProvingKey.lean` test](../tests/ProvingKey.lean) matches every extracted
coordinate and coefficient, rejects malformed point/polynomial encodings, and
optionally authenticates and decodes the entire uncompressed key passed as a
test argument. The full-key test also rejects a same-sized one-byte mutation.

On-curve checks alone do **not** establish that G2 points lie in the required
prime-order subgroup. The parser does not evaluate the NQR-7 FFT, perform MSM,
derive the H polynomial, produce a randomized proof, serialize it for Solidity,
or verify a pairing. The pinned key's origin and trusted setup remain external
assumptions even when its bytes match the published hash. The isolated
experimental worker uses this parser through the complete proof pipeline;
development exercises only public unfunded fixtures.
