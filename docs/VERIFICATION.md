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
and mathematical-workspace builds, pinned Mathlib dependencies, and every
theorem's axiom report. It writes `reports/verify-kernel.json` with
`PROOFS_CHECKED_ONLY` when those checks pass.

It does not run crypto compatibility vectors, OS/effect tests, local EVM
integration or complete public proof fixtures. It does not replace or update
`reports/verify.json`. The successful status deliberately differs from the
full regression verdict.

The proof-only workspace has its own pinned Mathlib dependency and transitive
manifest. It is not imported by the executable. See its [setup and targeted
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

The [local EVM suite](LOCAL_EVM_SCOPE.md) independently checks native calldata
and public proof fixtures against actual Solidity account/paymaster/verifier
code using synthetic local state. Its compiler/source dependencies and the
limits of its synthetic EntryPoint and pools are documented there.

## Full regression gate

```sh
node scripts/verify.mjs
```

The full gate builds executable/test targets, checks native boundaries and
independent fixture oracles, inspects every theorem, runs focused and full-size
public proof fixtures, runs mathematical and local EVM regressions, checks
synthetic provenance/integrity failures, and compares the supported CLI surface
with the pinned TypeScript oracle. Mathematical checks include the actual G1
windowed MSM's original-input weighted-sum theorem. It writes `reports/verify.json`
with `PASS_WITH_LIMITATIONS` only after every required check passes.

The source checkout for the TypeScript oracle, pinned local Solidity checkout,
Foundry and cached compiler versions must be available as specified by the
corresponding test scripts. Full native proof/key checks can take several
minutes each. No real funded transaction is part of this gate.

## Interpreting evidence

A full report identifies its exact input hashes and the CLI/worker bytes
snapshotted before tests and checked again before the verdict. After changing source, a prior
successful report is not evidence for that new source. A focused success
establishes only that check's scope; a kernel-only success establishes neither
compatibility nor physical IO behavior. The [security contracts](SECURITY_CONTRACTS.md)
and [proof scope](PROOF_SCOPE.md) distinguish acceptance invariants,
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
