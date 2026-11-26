# Protected storage boundary

The native CLI uses [`tornado_private_io.c`](../native/tornado_private_io.c) for exclusive note-backup creation and private-file reads. Lean 4.29.1 does not expose the required mode, `O_NOFOLLOW`, inode, link-count, ACL, or `fsync` operations. This small POSIX binding is therefore an explicit trusted component outside the Lean kernel proofs.

The binding opens each absolute-path ancestor through a directory descriptor, rejects symlinks, `..`, unsafe ownership and group/other-writable mode, and accepts safe `.` components. It rejects macOS ACL **allow** entries on every ancestor and leaf; mode `0600` alone is insufficient on APFS because an inherited ACL can grant access. It accepts deny-only ACLs, such as a home-directory deny-delete rule. New files use `O_EXCL | O_NOFOLLOW | O_CLOEXEC`, mode `0600`, regular-file/owner/single-link checks before and after writing, file `fsync`, and parent-directory `fsync`. Reads check regular file, owner, private mode, single link, size (at most one MiB), stable inode/size/timestamps, and no ACL grants. The binding never logs file contents.

The per-note claim wrapper additionally calls `checkPrivateDirectory` on its `claims/` and `attempts/` directories. This third FFI entry point requires current-user ownership, exact mode `0700`, no ACL grants, and the same descriptor-based ancestor checks. Claim filenames contain nullifier hashes, so a listable directory would expose information even when individual files are mode `0600`.

The [regression test](../scripts/test-protected-io.mjs) exercises exclusive creation, mode, symlink parents and leaves, hard links, traversal, public files, safe `.` components, and on macOS both an inherited directory ACL and a direct file ACL. The [claim test](../scripts/test-note-claims.mjs) rejects listable directories and tests a two-process exclusive race. The ACL regressions reject inherited and direct access grants. These tests do not prove that the OS or storage device honors `fsync` under every crash, or that same-user malicious processes cannot race or inspect this process's memory.

`notes create` and `notes create-plan` write exclusively through this binding; `notes inspect` and `notes invoice` read through it. Their paths can be absolute or relative to the working directory; `..` path components are rejected.

Mutable journals use protected byte-for-byte compare-and-replace under an
exclusive same-directory lock: a new private inode is written/synced, renamed
atomically, and the parent directory is synced. Exact removal checks the
unchanged protected file before unlinking and syncing its directory. A stale
lock after a crash fails closed and requires investigation. Shared sender
locks and exclusive opaque per-note claims are connected to experimental send
adapters. Batch mirror updates preserve candidate evidence and an authoritative
in-progress marker across partial writes. Signed operations and proof payloads
can be executable at a simulation RPC, bundler or relayer, so reservation and
exposure marking precede those calls. Fault tests exercise write/CAS errors,
concurrent claims and unknown outcomes; they do not prove whole-workflow crash
safety or actual hardware durability.

The runtime-used withdrawal journal and batch repair now share a finite
create/CAS interpreter with exact-command acknowledgement certificates and
conditional crash-prefix/readmission theorems. Native admission treats only
ENOENT as absence and blocks partial or unreadable claims. The physical model
explicitly includes interrupted creates and lost replies; its storage contract
remains an assumption about this C/OS boundary. Five test-only native process
cuts exercise the actual C implementation without adding a production fault
mode. See [reservation and restart scope](RESERVATION_RECOVERY_SCOPE.md).

The native C source, Lake linker configuration, and tests are hashed into the
verifier's input inventory. The verifier checks an exact explicit FFI allowlist
for protected storage, HTTPS, entropy, process and native signing boundaries;
it rejects undeclared `opaque` or `extern` declarations in project Lean source.
