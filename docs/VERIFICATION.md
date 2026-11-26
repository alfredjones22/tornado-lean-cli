# Running the verification checks

Use the repository's pinned Lean toolchain and Node 22.18 or newer. The
standalone executable remains native Lean; Node is development tooling for
the checks and independent compatibility oracles.

## Kernel and source gate

```sh
node scripts/verify.mjs --kernel-only
```

This checks the toolchain, source/test inventory, pinned proving assets,
declared native boundary, absence of proof escapes, all runtime/pure-library
and both proof-workspace builds, pinned Mathlib dependencies/local paths, and every
theorem's axiom report. It writes `reports/verify-kernel.json` with
`PROOFS_CHECKED_ONLY` when those checks pass.

It does not run crypto compatibility vectors, OS/effect tests, local EVM
integration or complete public proof fixtures. It does not replace or update
`reports/verify.json`. The successful status deliberately differs from the
full regression verdict.

The mathematical and application proof workspaces share the same pinned
Mathlib dependency and transitive revisions. Neither is imported by the
executable. See its [setup and targeted
cache instructions](../proofs/README.md); the G1 group bridge uses
`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`.

The mathematical checks use official precompiled Mathlib caches at the pinned
revisions. Project proof source and axiom reports are checked against imported
library artifacts; this is not a fresh source rebuild of every dependency.
Imported dependency/build artifacts and the compiler remain trusted.

## Focused checks

Examples of pure focused checks are:

```sh
lake env lean --run tests/AbiDecode.lean
lake env lean --run tests/BatchWithdrawalIntent.lean
lake env lean --run tests/ByteEntropy.lean
```

Modules which exercise native private-file, signing or process boundaries
need their compiled Lake test targets. Their correct invocation is recorded
in `scripts/verify.mjs`; interpreter-only execution does not supply linked
native symbols. Worker tests use protected temporary directories under
`tests/`, not the shared `/tmp` path.

TLS regression coverage is platform-dependent. The GET tests reject untrusted
certificates on macOS, but its system libcurl does not use the temporary
`CURL_CA_BUNDLE`, so the trusted-local-fetch case is skipped there. On supported
Linux libcurl builds, that case also exercises decoding, body caps, redirects,
HTTP status and cache headers. Production code retains the system trust store;
there is no test-only CA bypass in the transport.

The local EVM suite independently checks native calldata and public proof
fixtures against actual Solidity account/paymaster/verifier code using
synthetic local state; its prerequisites and boundaries are described below.

## Full regression gate

```sh
node scripts/verify.mjs
```

The full gate builds executable/test targets, checks native boundaries and
independent fixture oracles, inspects every theorem, runs focused and full-size
public proof fixtures, runs mathematical and local EVM regressions, checks
synthetic provenance/integrity failures, and checks catalog/planner/note-file
outputs against pinned independent regression references. These are finite
checks, not an obligation to reproduce another CLI's behavior. Mathematical checks include complete native transforms, both group/MSM
constructions, assembly, pairing and source-level worker-output results.
The public witness certificate is regenerated and checked against every R1CS
row; the independent point schedule and structural mutations are also tested. It writes `reports/verify.json`
with `PASS_WITH_LIMITATIONS` only after every required check passes.

The development-only reference checkout identified by `scripts/oracle-identity.mjs`,
the pinned local Solidity checkout, Foundry and cached compiler versions must
be available as specified by the corresponding test scripts. Historical
reference hashes remain in the fixture manifests for reproducibility; they
do not define the CLI's current specification. Full native proof/key checks can take several
minutes each. No real funded transaction is part of this gate.

## Local EVM interoperability

```sh
node scripts/test-local-evm.mjs
```

This runner compiles pinned sources offline, checks source/compiler/bytecode
hashes against [`artifact-provenance.json`](../fixtures/evm/artifact-provenance.json),
starts its own Anvil on an ephemeral loopback port with chain ID 31337, and
cleans up its server and compiler output. It accepts no RPC/fork URL, private
key or network-broadcast option.

The standalone suite needs Node 20+, the pinned Lean toolchain and compiled
imports, `forge`, `cast`, `anvil`, and cached solc 0.7.6 and 0.8.28. The reference
Foundry installation is v1.6.0 nightly; compilation uses `forge build --offline`.
Account/paymaster sources must exist at `../kohaku-contracts/privacy-paymaster`
or `TORNADO_EVM_CONTRACTS_SOURCE`. Checked revisions are privacy-paymaster
`1b23e91a06fb4af50220507febf38bd05078e6a4`, account-abstraction
`4cbc06072cdc19fd60f285c5997f4f7f57a588de`, and OpenZeppelin
`5fd1781b1454fd1ef8e722282f86f9293cacf256`.

The fixture pins every transitive Solidity source, compiler, optimizer and
metadata setting, and creation/runtime hashes before constructor-immutable
patching. Classic Verifier uses solc 0.7.6/Istanbul; other contracts use
0.8.28/Cancun, with 200 optimizer runs and metadata hash `none`. Deliberate
regeneration after reviewing a source change uses
`node scripts/build-local-evm-fixtures.mjs --pin`.

The suite has 133 assertions. Actual Classic verifier code accepts three public
proofs and rejects all eighteen single-public-signal mutations. Actual
SimpleAccount/factory/proxy code exercises native deployment/batch calldata,
owner authorization, ordered calls and rollback. Actual paymaster validation
and `postOp` exercise sponsor recipient/fee binding and a controlled refund.
The native sponsored batch builder supplies a checked public proof and exact
net-forwarding suffix; a synthetic ledger rejects a repeated public nullifier.

Deposit cases use actual `DepositMulti.publicItems`, the certified planner and
`DepositBatch7702.callsData` against independently pinned commitments/amounts.
They check ordered ETH deposits and a six-note synthetic token plan's four-plus-
two split, exact allowance, reset-before-approve, zero ETH on token deposits,
remaining chunk budget and deficient-balance rejection. These token notes are
relabelled public fixtures; no spend proof is generated for them.

Simple7702 deposit execution uses the exact hashed runtime in
[`simple7702-code.json`](../fixtures/simple7702-code.json), placed at synthetic
senders. Its source compilation is not reproduced by the compiler-provenance
step, and the fixed EntryPoint caller is impersonated. Account/paymaster
addresses and storage are also placed synthetically; this does not authenticate
live deployment identity.

EntryPoint, tokens, pools and ledgers are synthetic. The ETH ledger uses a fixed
root and real verifier, not the full Classic deposit/Merkle contract; the token
pool does not verify proofs. Validation, execution and `postOp` are called
separately. The suite does not run full `handleOps`, validate owner signatures,
check EntryPoint gas accounting/deposits, nonce/replay or bundler ERC-7562 rules,
authenticate chain history, verify a token-price oracle, or establish EIP-7702
authorization/delegation lifecycle behavior.

Imported paymaster sources retain their `UNLICENSED` notices. They are compiled
from the local pinned checkout into a temporary directory and are not vendored.
The synthetic harness's MIT license does not change those source licenses.

## Interpreting evidence

A full report identifies its exact input hashes and the CLI/worker bytes
snapshotted before tests and checked again before the verdict. After changing source, a prior
successful report is not evidence for that new source. A focused success
establishes only that check's scope; a kernel-only success establishes neither
compatibility nor physical IO behavior. The [security specification](SECURITY_SPEC.md)
and [proof coverage](PROOFS.md) distinguish acceptance invariants,
construction theorems, finite test evidence and external assumptions.

After a fresh full gate, [build provenance](BUILD_PROVENANCE.md) can record
those tested executable bytes and assets. The independent checker hashes
candidate files without executing them, using a manifest digest obtained from
an independently trusted source. A local fresh-build comparison is evidence
for those two builds, not cross-platform bit reproducibility. Neither a
self-hash nor a successful report authenticates a release or pins the worker
used by a later invocation.

All reports are generated local artifacts under the ignored `reports/`
directory. They are not certifications of bug-free code, loss-free operation,
Ethereum consensus, deployed-contract identity or implementation zero knowledge.
