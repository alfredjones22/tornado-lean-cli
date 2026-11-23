# Native gzip and DEFLATE scope

[`Gzip.lean`](../Tornado/Compression/Gzip.lean) is a pure Lean decoder for one
gzip member containing RFC 1951 DEFLATE. It handles stored, fixed-Huffman and
dynamic-Huffman blocks, optional extra/name/comment/header-CRC fields, the
gzip data CRC32, and ISIZE. It rejects malformed Huffman trees, missing
end-of-block codes, reserved symbols and block types, bad backreferences,
invalid stored-block lengths, truncated data, and trailing bytes or additional
gzip members. The generic decoder caps both input and output at 32 MiB and
limits a member to 4,096 DEFLATE blocks; fixed Huffman tables are reused
within the member. These are resource guards, not a formal runtime bound.

`pinnedCircuit` and `pinnedProvingKey` first check the SHA-256 of the compressed
asset, then decompress with the exact expected output length and check the
uncompressed SHA-256. They are suitable for the two bundled public proving
assets only. Both compressed and uncompressed digests are hard-coded from the
pinned SDK assets. No zlib or native decompression FFI is used at runtime.

The [vector generator](../scripts/generate-gzip-vectors.mjs) uses development
Node zlib to produce deterministic public streams. The Lean
[`Gzip.lean` test](../tests/Gzip.lean) covers six streams, including stored,
fixed and dynamic blocks, optional gzip header fields, multiple fixed blocks,
CRC/size corruption, truncation, reserved flags/types, and output bounds. A
zlib-valid member with 4,097 empty fixed blocks must fail at the block cap.
The compiled test also decompresses and authenticates the complete pinned
19,474,889-byte circuit and 14,522,256-byte proving key. This whole-asset
run took several minutes in recorded tests; interpreter mode is much
slower and uses substantially more memory.

The kernel-checked `verifyTrailer_sound` and `decompress_success_integrity`
theorems show that a successful return passed the caller output limit, ISIZE
comparison, and CRC32 comparison. They depend only on Lean's standard
`propext` and `Quot.sound` axioms. They do **not** prove that the DEFLATE
algorithm reconstructs every valid stream correctly, that CRC32 or SHA-256
is collision resistant, or that the assets came from a secure trusted setup.
Finite zlib comparisons and pinned-asset hashes provide compatibility
evidence. The caller must still parse/authenticate the decoded circuit and
key and bind them to the same proof operation.
