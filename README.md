# Tornado CLI in Lean

MIT licensed. Copyright (c) 2026 Tornado. See [LICENSE](LICENSE).
Vendored dependencies and reference fixtures retain their original license notices.

> **Best-effort formal verification does not guarantee bug-free code or prevent every loss of funds.** Proofs cover selected properties under stated assumptions. The native C/OS boundaries, external services and complete command behavior are not fully proved. The isolated Lean note prover and note-derived signer use variable-time arithmetic and do not guarantee secret erasure.

This repository contains a standalone Tornado CLI implemented in Lean. Its
protocol implementation was developed with the goal of reproducing the
functionality of `@kohaku-eth/tornado-cash@0.1.0-alpha.40` in pure Lean, including
protocol parsing, cryptography and proof generation. Protected account-key
signing and OS services use the native boundaries described in
[Trust boundaries](docs/TRUST_BOUNDARIES.md).

CLI Functionality should mirror the
[New Era Tornado UI](https://github.com/alfredjones22/tornado-ui-new-era). It supports independent or mnemonic-derived
notes, denomination planning, sequential or delegated deposits, sponsored or
Classic relayer withdrawals, smart-account contract calls, status, recovery,
history and compliance reports. Lean is pinned to `leanprover/lean4:v4.29.1`.

## Build and run

```sh
lake build tornado tornado_prover_worker
lake exe tornado --help
lake exe tornado pools --chain 1 --asset ETH
lake exe tornado deposit plan --chain 1 --asset ETH --amount 1.4
lake exe tornado notes create --chain 1 --denom 0.01 --count 1 --out ./notes.txt
lake exe tornado deposit send --notes-file ./notes.txt --key-file ./key.txt --chain 1 --dry-run
lake exe tornado withdraw one --note-file ./notes.txt --recipient 0xRecipient --chain 1 --dry-run
```

Replace the recipient placeholder with the intended address. Creating notes
writes a new protected backup; keep it before funding its commitments. Account
key files contain a raw `0x`-prefixed private key and require mode `0600`, safe
ownership and no access-granting ACLs. Omit `--key-file` or `--owner-key-file`
for hidden terminal entry when supported; private keys are handled inside the
protected native signer boundary.

Deposits and withdrawals default to mainnet. Select `--chain 11155111` for
Sepolia notes. Run `--dry-run` and review the network, amounts, recipient, fees
and calls before a separate `--broadcast` command. Typed approval is the default;
`--non-interactive` explicitly authorizes unattended sending and requires
protected key files for account-key routes. It retains review output,
validation, journals, reservations and uncertain-outcome handling.

A single-note deposit defaults to an ordinary transaction. `--delegated`
forces the UserOperation route; multi-note deposits can automatically reuse the
compatible delegation. Withdrawals can forward proceeds or execute ordered
contract calls from a recoverable smart account. See [Usage](docs/USAGE.md) for
supported combinations, options and limits.

Keep original backups, journals and status files. After an uncertain outcome,
reconcile the recorded candidate before retrying. A failed sponsored execution
can leave the sponsor note spent and funds in the smart account. The
[Recovery guide](docs/RECOVERY.md) covers deposit resume, status and sweeps.

## Documentation

- [Usage](docs/USAGE.md): commands, private files, networks and operating limits.
- [Security specification](docs/SECURITY_SPEC.md): intended fund-safety and disclosure rules.
- [Proof coverage](docs/PROOFS.md): proved properties, source pointers and remaining gaps.
- [Recovery](docs/RECOVERY.md): interrupted operations, reservations, journals and smart accounts.
- [Trust boundaries](docs/TRUST_BOUNDARIES.md): signing, proving, filesystem and external-service assumptions.
- [Verification](docs/VERIFICATION.md): reproduce the checks and interpret their scope.
- [Build provenance](docs/BUILD_PROVENANCE.md): compare executable and asset bytes against a trusted manifest.

The configured history RPC can learn deposit–withdrawal linkage through selected
deposit-receipt and nullifier-spent queries. Internally consistent RPC replies
can still be false, and one observed inclusion is not Ethereum finality.

## Reusable cryptography and proofs

The [LeanCrypto package](packages/lean-crypto/README.md) contains the reusable
hashes, key tools, encoding, sampling, BN254 and generic Groth16 components. It
has no application, native signing or Mathlib dependency. Its documentation and
[standalone consumer](packages/lean-crypto/tests/StandaloneConsumer.lean) explain
how other Lean projects can use it and which limitations remain.

The separate [mathematical workspace](proofs/README.md) and
[application proof workspace](app-proofs/README.md) use pinned Mathlib. Their
results include arithmetic and construction theorems plus a conditional
proof-output privacy bound; they do not establish whole-process secrecy,
constant-time execution or end-to-end wallet correctness.

## Verification

With Node 22.18 or newer:

```sh
node scripts/verify.mjs --kernel-only
node scripts/verify.mjs
```

The kernel-only gate writes `PROOFS_CHECKED_ONLY`; the full regression gate
writes `PASS_WITH_LIMITATIONS` only when its required checks pass. The full
gate uses public fixtures and injected submission effects, not funded network
transactions. Reports under `reports/` are generated local artifacts bound to
exact input hashes. See [Verification](docs/VERIFICATION.md) for prerequisites,
independent reference dependencies and the difference between proofs and tests.
