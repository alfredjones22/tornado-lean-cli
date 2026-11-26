# Trust boundaries

The Lean theorems constrain selected source definitions under explicit
assumptions. They do not establish that every native effect, provider reply,
compiler transformation or hardware action meets those assumptions. Read the
[security specification](SECURITY_SPEC.md) and [proof coverage](PROOFS.md)
alongside these boundaries.

## Account-key signing

Deposits, batch-owner signing and smart-account recovery use the protected
[native signer](../Tornado/Runtime/NativeSigner.lean). Lean passes a protected
key-file path or public interactive-session alias and the exact signing
digest. Private-key bytes are not returned to Lean. The bridge uses pinned,
unmodified [libsecp256k1](../native/vendor/libsecp256k1/UPSTREAM.md), verifies
the low-S signature and recovered identity, and rejects failed controls or
recovery IDs 2 or 3. Lean binds the returned identity/signature to the reviewed
sender and serialized operation.

The [C wrapper](../native/tornado_secret_sign.c) loads keys into a locked
native page, disables process core dumps, requests no-dump handling where
supported, randomizes each signing context from OS entropy and explicitly
clears/releases its buffers on handled exits. libsecp256k1 is designed for
constant-time secret-key operations; this is not a theorem about the complete
wrapper/compiler/hardware combination. Clearing is best effort and does not
guarantee erasure of every copy or behavior after abrupt termination.

Raw key files are limited to 1,024 bytes; encrypted Web3 Secret Storage v3
JSON files have a separate bounded loader. Both satisfy owner, mode,
single-link, no-symlink, stability and platform ACL checks. Raw keys use a
`0x`-prefixed 32-byte hexadecimal value.
Native diagnostics identify fixed failure categories without returning key
bytes, file content, digest, filename or OS error numbers.

Encrypted account files are parsed and decrypted inside the native boundary.
OpenSSL libcrypto supplies PBKDF2, AES-128-CTR and Ethereum Keccak-256;
libsodium supplies scrypt, including historical Geth parameter combinations.
The MAC is checked before plaintext is admitted, the secp256k1 scalar is
validated and any stored account address must agree. The unlocked key stays in
a locked command-local native session, and protected source-file checks guard
later signing against changed content or metadata. No decrypted key is returned
to Lean or written to disk; the original path still anchors reservations.

Hidden passwords and protected password-file contents stay native; Lean
receives only the file path and public policy flags. KDF workspaces and the
OpenSSL/libsodium internals are additional trusted memory outside the locked
key page; their clearing and the OS remain best
effort. Format/authentication tests do not prove constant-time whole-command
behavior or secure erasure. See [Usage](USAGE.md#encrypted-account-keystores).

Hidden entry reads `/dev/tty` with echo disabled, parses the key in C and
keeps it in the locked command-local session. It creates no key file and does
not put the key in Lean strings, command-line arguments or environment values.
Normal finalization clears the session; handled signals during key entry restore
the terminal and clear pending input, and pasted typeahead is flushed before approval.
Abrupt exits still rely on OS reclamation/no-dump protection. This session is
single-threaded command support, not a general concurrent key vault.

Unattended account-key commands require an explicit protected key file.
`--non-interactive` skips typed approval, not the native signer, journal,
reservation or revalidation checks. The C code, libsecp256k1, compiler, OS,
protected filesystem and security of the original key source remain trusted.

## Note secrets and the prover worker

Note creation, backup inspection and the isolated prover use Lean-managed
secret values. The separate
[worker](../Tornado/Cli/ProverWorkerMain.lean) handles note preimages,
witnesses, FFT/MSM intermediates and blinding scalars with variable-time,
nonzeroizing arithmetic. Process isolation shortens their lifetime but does
not establish constant-time execution, secure erasure or protection against
same-user memory inspection.

Direct one-note 4337 withdrawal also derives a signing key from the note's
secret data in [ProverWorker](../Tornado/Cli/ProverWorker.lean). This applies
to traditional random notes as well as notes created from a mnemonic. Its
ECDSA signing remains Lean. Classic relayer withdrawal does not use that
note-derived transaction signer; batch withdrawals use the owner-key native
boundary. Protecting only ECDSA would not harden the rest of the witness/prover.

In proof-generation mode, the child authenticates circuit, proving-key, graph
and certificate inputs before opening its protected note. It checks selected note identity, Merkle
membership, field bounds and reviewed public signals. The parent never reads
the note in this withdrawal path: it accepts bounded canonical metadata or
proofs, checks request bindings, decodes all proof points and verifies against
the compiled Classic key before constructing calldata. Route policy, chain
state and fee/account validation still belong to the parent.

The restricted program has only configured reads and proof-mode 32-byte
entropy draws. Public requests are capped at 4,096 bytes. Compressed circuit,
key and graph slots are capped at 4/32/16 MiB; the public witness certificate
has a 2 MiB compressed and 16 MiB decompressed cap. The protected private-note
reader supplies its separate limit. The parent caps child runtime/output,
rejects malformed/noncanonical wire records and does not echo worker stderr
or parsed note content. A fatal process crash can bypass sanitized handling.

The launcher caches the first observed child exit status and does not wait
on a reaped process or signal a potentially reused process identifier.
These process controls and finite tests do not prove complete physical IO
refinement. Core-dump suppression must succeed before worker input access.

The CLI launches the sibling `tornado_prover_worker`; its installation is
trusted, not authenticated at runtime. A substituted worker receives the
protected note path and could read/disclose the note. That path is also
visible in process arguments. [Build provenance](BUILD_PROVENANCE.md) can
check artifact identity against an independently trusted manifest, but does
not force a later invocation to use the checked worker.

## Files, claims and crash behavior

The [private-file binding](../native/tornado_private_io.c) traverses ancestors
through directory descriptors. It rejects symlinks, `..`, unsafe ownership
and group/other-writable ancestors, while permitting safe `.` components.
On macOS, access-granting ACLs on ancestors or leaves are rejected; deny-only
ACLs are allowed. Linux relies on mode bits and does not explicitly inspect
every ACL implementation. Mode `0600` alone is insufficient when a macOS ACL
grants access.

Private creation uses exclusive/no-follow/close-on-exec flags, mode `0600`,
owner/regular-file/single-link checks, file sync and directory sync. Reads
check owner/private mode, one link, bounded size (at most one MiB), stable
inode/size/timestamps and platform ACL policy. Claim/cache directories require
current-user ownership, exact `0700` and no access-granting ACLs. Filenames can
contain sensitive associations even when individual file content is private.

Mutable records use exact byte-for-byte compare-and-replace with a
same-directory lock, a new synced private inode, atomic rename and directory
sync. Exact removal checks the unchanged protected file before unlinking.
Stale locks fail closed. The physical model admits partial interrupted
creates and writes that complete before a lost reply; it does not prove an
OS or device actually honors those contracts.

Claims coordinate one local reservation/status/key directory. Copies,
manual deletion, hostile same-user changes and storage corruption are outside
that coordination. Native fault tests and conditional crash-prefix theorems
add evidence, not a guarantee of durable storage or global uniqueness of
signing. [RECOVERY.md](RECOVERY.md) explains safe reconciliation.

## HTTPS and provider responses

Native [HTTPS](../native/tornado_https.c) uses system libcurl/TLS trust.
Remote endpoints must use HTTPS. Explicit loopback HTTP is accepted only
when both URL spelling and actual socket destination are loopback. Remote
plaintext, credentials, ambient proxies and redirects are rejected; the GET
boundary also rejects fragments, oversized headers, non-200 responses and
responses beyond its supplied cap. HTTP authentication and netrc are disabled.

The transport has a 10-second connect timeout, 30-second POST timeout and
60-second GET timeout. libcurl may decode HTTP content encoding before its
bounded callback; Saga validation accepts bounded decoded bytes or raw gzip.
These controls authenticate the configured endpoint and bound resource use.
They do not authenticate its Ethereum claims or hide requests from it.

Malformed, oversized, noncanonical or inconsistently bound JSON/ABI data is
rejected locally. An internally consistent fabricated chain can still pass.
Chain IDs, hashes, receipts, logs and exact-block calls are provider evidence,
not authenticated state proofs against a locally verified consensus root.
One observed inclusion can reorganize. Deployed pool/verifier/account code,
contract behavior and consensus/finality remain assumptions. A false unspent
reply does not prove absence of a competing pending spend.

## History validation and privacy

**The history RPC is trusted with deposit–withdrawal linkage.** Selected
deposit receipt requests and selected-nullifier `isSpent(bytes32)` calls can
be correlated by an operator. The latter discloses the nullifier hash before
withdrawal, even when the answer is false. Pool-wide log filters do not remove
this association, and a proxy does not itself provide query privacy.
Compliance reports are redacted and protected, but still contain sensitive
deposit associations.

The default Saga proxy is `https://saga.0000000000.org` with `/sepolia` for
Sepolia. Chunks are checked against the fetched index with bounded gzip,
SHA-256, strict event ABI, ordering and gap-free coverage. The index is not
independently signed: a matching checksum proves index/chunk consistency,
not canonical chain history. A failed Saga attempt discards its partial
result before bounded RPC fallback.

History limits include a five-minute aggregate deadline, 4,096 RPC requests,
256 MiB aggregate response bytes and 256 MiB decoded Saga bytes, one MiB per
RPC response, two MiB per index, 32 MiB per compressed/decoded chunk, 64 Saga
segments, one million combined events and two million RPC-scanned blocks.
RPC log windows are at most 1,000 blocks and range failures may be bisected
at most ten levels. Deadlines are checked between requests; an in-flight
request can extend beyond the aggregate deadline by its own timeout.

Pinned local snapshots authenticate exact compiled hashes/schema and rebuild
the deposit root. Native caches contain public history, not note preimages,
and use content-addressed chunks of at most one MiB with a protected index.
Checkpoint count/root and, for caches, block hash are rechecked at that
height. Unavailable or disagreeing old state causes rebuild; malformed or
tampered present files, malformed replies, wrong chains and budget failures
still stop. Missing assets permit bounded rebuild rather than unchecked use.

The [snapshot loader](../Tornado/Runtime/HistorySnapshot.lean) additionally caps
decoded pinned assets at 128 MiB, aggregate cache chunks at 256 MiB, chunks at
4,096 and records per chunk at 1,000. Deposit trees have at most `2^20` leaves.
Exceeding these limits stops rather than admitting incomplete state.

Cached history drops stored finality claims and replays the 7,200-block
overlap. The assets/cache adapter permits one bounded new-head catch-up and
checks head hashes before saving. Required current count/root checks remain;
the sync never invents a finalized cursor. A deposit root/count does not
detect every omitted withdrawal. Selected-note spent/receipt checks are still
required; cache success alone cannot authorize a spend or prove completeness.

## Proof dependencies and cryptographic assumptions

The Lean kernel, compiler, runtime integer/byte semantics, imported artifacts
and native FFI implementations remain trusted. The verification gate checks
an explicit FFI allowlist and source inventory; this does not prove the C
implementations. Runtime `LeanCrypto` has no Mathlib dependency. The separate
proof workspaces use pinned Mathlib/transitive revisions and may import
official precompiled caches rather than rebuilding every dependency source.

Honest setup/query/key relations, IID uniform entropy independent of witnesses,
cryptographic hardness and selected finite-point/source conditions remain
explicit hypotheses. Digests authenticate bytes, not setup honesty. Algebraic
verifier completeness is not proof-system soundness or proof of deployed
Ethereum verifier equivalence. The conditional proof-output bound excludes
timing, memory, arbitrary parser failures and other worker modes.

The gate rejects custom global axioms, `sorry`, `admit` and unapproved proof
escapes in project proofs; accepted reports list standard Lean axioms where
used. [VERIFICATION.md](VERIFICATION.md) explains report scope and dependency
setup. None of these checks certifies complete secret erasure, constant-time
execution, all-command correctness, API truth or loss-free operation.
