# Build provenance and independent integrity checks

The provenance manifest records the exact CLI, isolated prover worker,
compressed proving assets, public verification inputs, and observed build
environment associated with a fresh full verification report. It preserves
that report's `PASS_WITH_LIMITATIONS` status. It does not certify production
fund safety, privacy, compiler correctness, or executable authenticity.

The manifest and its SHA256 must come from an independently trusted source.
A digest printed by an untrusted manifest generator, downloaded beside an
untrusted binary, or recomputed from an untrusted manifest provides no
independent authenticity. These tools do not implement signatures, a release
trust service, runtime worker pinning, or an authenticated installer.

## Record a verified build

After the full verification gate finishes on frozen sources:

```sh
node scripts/build-provenance.mjs record --output reports/build-provenance.json
```

The report must be a full, successful `reports/verify.json`, completed within
one hour by default. Kernel-only, failed, running, future-dated, stale, or
incomplete reports are rejected. `--max-age-seconds` explicitly selects a
freshness window from 1 to 86400 seconds; timestamps depend on the host clock.
The output must be a new filename under `reports/`.

The verifier must snapshot both executable hashes and sizes **after building
and before running native tests**, require that those bytes remain unchanged
at the final gate, and include them in `buildArtifacts`:

```json
{
  "cli": {"path": ".lake/build/bin/tornado", "sha256": "...", "size": 123},
  "worker": {"path": ".lake/build/bin/tornado_prover_worker", "sha256": "...", "size": 456}
}
```

The generator compares the current artifacts with these tested-byte records.
A newer or substituted executable cannot acquire a provenance record from
an earlier report. Every reported input hash is rechecked, including after
collecting environment metadata and hashing artifacts. All current Lean and
native C/header sources outside hidden directories, build caches,
`node_modules` and `reports` must appear in the verified inventory, and the
number of Lean files must agree. The executing generator must match its
verified source hash. The CLI and worker are read as data, never executed by
the provenance generator.

The manifest records:

- CLI and worker SHA256 and byte sizes, plus the compressed asset hashes,
  sizes, and previously verified raw-asset descriptors.
- Every public verification input and a canonical digest of that inventory.
  `sourceContentSHA256` covers the listed Lean, native, script and build
  configuration inputs, using sorted `path NUL SHA256 NUL size LF` records.
  These explicit inventories define the digest scope; arbitrary untracked
  working-tree files are not represented as verified content.
- Lean toolchain and observed Lean/Lake/C compiler versions, the compiler
  executable hash, Node versions, OS release, architecture, and machine type.
- Git HEAD, branch and dirty state as informational metadata. Content hashes
  bind dirty working-tree inputs; a commit label does not identify them.

The generator reads only explicitly registered public verification inputs,
not `.env`, key stores, hidden directories or arbitrary private files.
Symbolic links, unsafe relative paths, missing inputs, new unverified Lean
or native sources, and concurrent changes detected during hashing fail the
recording. Build tools, the verifier and report, Node, filesystem behavior,
and the host remain trusted. The recorded environment describes the host
at recording time; it is not a compiler or build-process attestation.

## Check candidate artifacts without executing them

Obtain `TRUSTED_MANIFEST_SHA256` independently and use a separately trusted
copy of `check-build-integrity.mjs`:

```sh
node scripts/check-build-integrity.mjs \
  --manifest release-build-provenance.json \
  --manifest-sha256 "$TRUSTED_MANIFEST_SHA256" \
  --cli /candidate/tornado \
  --worker /candidate/tornado_prover_worker \
  --asset-root /candidate
```

The asset root contains the manifest's relative `assets/proving/...` paths.
The checker uses only Node filesystem, path and SHA256 operations. It does
not import or invoke the CLI, worker, native libraries, generator, Lean or
Lake. It checks the independently trusted manifest digest first, then every
candidate's exact hash and size. Missing or changed candidates, symbolic
links, duplicate asset paths, malformed records and traversal paths fail.
This establishes byte identity with the trusted manifest at checking time.
Dynamic system libraries are outside the candidate-file checks. It does
not authenticate the manifest or checker, reserve the files against
later replacement, or force the runtime to use the checked worker.

## Compare a fresh build on the same host

Prepare a separate directory containing the recorded public source inputs
and assets. Give it a fresh build directory and use the same installed
toolchain and build configuration. Build the CLI and worker there; preserve
the original build cache and verification report. Then compare directly:

```sh
node scripts/build-provenance.mjs compare \
  --first reports/build-provenance.json \
  --manifest-sha256 "$TRUSTED_MANIFEST_SHA256" \
  --candidate-root /path/to/fresh-build
```

This mode checks the baseline input inventory against the fresh directory,
checks the recorded toolchain/platform descriptors, and compares binary and
asset bytes. It does not require a new verification report and does not
issue a new verification verdict. A difference prints a failure, including
the expected and observed digest for a changed executable.

Two separately recorded manifests can also be compared with `compare
--first first.json --second second.json`. Their timestamps, run IDs and Git
dirty flags may differ; source inventories, toolchain/platform descriptors,
CLI, worker and asset bytes must agree.

An equal local rebuild is evidence for those two builds only. Different
linkers, SDKs, system libraries, paths, timestamps or other host inputs can
affect bytes. No cross-platform or universal bit reproducibility is claimed.
The scripts do not run a build or delete any cache automatically.

## Regression evidence

`node scripts/test-build-provenance.mjs` uses only public synthetic sources,
assets, fake gate reports and fake executable candidates. It checks positive
recording/integrity, stale and failed reports, missing or changed sources,
added unverified sources, post-test binary substitution, invalid manifests,
wrong trusted digests, tampered CLI/worker/assets, symbolic links, duplicate
arguments, and matching/different rebuilds. Candidate scripts would create
marker files if invoked; the tests require that no marker is created.
Synthetic reports do not constitute verification evidence for the real CLI.
