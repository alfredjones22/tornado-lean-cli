# Pinned Tornado proving assets

These compressed files come from the published `tornado-ui-new-era/dist/offline/proving` asset set used by the pinned CLI/SDK release. The native Lean prover worker reads them through `WithdrawProof.loadAssets` and the Classic proof pipeline. It authenticates the compressed bytes, decompresses them in Lean, checks the raw hashes and circuit/key structure, constructs the witness, and verifies the generated proof with the compiled Classic key.

- `tornado-3ddd61dbff09caee.json.gz`: 19,474,889 bytes decompressed; SHA-256 `3ddd61dbff09caeec82d8edde95c674a3c34f9e66b1fe9f2c8783e72fe536f98`.
- `tornadoProvingKey-8e2d2f22beafb5a9.bin.gz`: 14,522,256 bytes decompressed; SHA-256 `8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af`.

The hashes and sizes match `tornado-cli-new-era/src/services/proving-manifest.json` at commit `daaa0c18de91ecc2effbdaea8d0bea7c856ff7f7`. `scripts/verify.mjs` checks the decompressed content. The worker also requires the authenticated graph at `fixtures/witness-vm-selected-components.json`, relative to its proving-assets root.

Public, unfunded fixtures exercise native proof generation and byte-for-byte SDK compatibility. These asset hashes do not establish trusted-setup security, correctness for every circuit input, deployed-verifier identity, constant-time execution or secret erasure.
