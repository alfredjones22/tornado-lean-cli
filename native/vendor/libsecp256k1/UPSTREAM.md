# Vendored libsecp256k1

This is the unmodified `include/`, `src/`, and `contrib/` tree from the official
[libsecp256k1 v0.8.0 release](https://github.com/bitcoin-core/secp256k1/releases/tag/v0.8.0),
plus its `COPYING`, `README.md`, and `CHANGELOG.md` files. The upstream MIT
license is in `COPYING`.

- Download: `https://github.com/bitcoin-core/secp256k1/archive/refs/tags/v0.8.0.tar.gz`
- Archive SHA-256: `eb52b0e9239dff7dc26be5f9623567141b8720ec47da29eb3c1e0a660d17c8bb`
- Annotated tag object: `18f07c42218765cd46148d74d9fe575795f56dce`
- Peeled release commit: `6e2c8bc4ecdc6e71dbe7a368f360d8d453ce435d`

Only `src/secp256k1.c`, `src/precomputed_ecmult.c`, and
`src/precomputed_ecmult_gen.c` are compiled. The build enables ECDSA recovery
and the upstream default 86 KiB signing table / 15-bit verification window.
It does not enable any other optional module. `lakefile.lean` records the
exact compiler options. The public Lean bridge is separately implemented in
`native/tornado_secret_sign.c` and is not part of upstream libsecp256k1.

To check provenance, download the archive, verify its SHA-256, extract it,
and compare `include/`, `src/`, `contrib/`, `COPYING`, `README.md`, and `CHANGELOG.md`
byte for byte with this directory. No generated build files or patches are
included here.
