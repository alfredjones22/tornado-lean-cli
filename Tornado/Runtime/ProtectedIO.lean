import Lean

/-!
The `extern` declarations form the explicit POSIX trust boundary.
`native/tornado_private_io.c` contains the implementations. These functions
reject symlinks, unsafe ancestors and public/hard-linked files. This is for
durable, append-only secret and attempt records; callers must choose unique
record names and never overwrite an attempt after network exposure.
-/

namespace Tornado.Runtime.ProtectedIO

@[extern "tornado_private_create"]
opaque createPrivate (path : @& String) (contents : @& ByteArray) : IO Unit

@[extern "tornado_private_read"]
opaque readPrivate (path : @& String) : IO ByteArray

/-- Compare-and-replace an existing protected file under a same-directory
    exclusive lock. The C boundary writes and syncs a new 0600 inode before
    atomic rename, then syncs the parent directory. A stale lock after a crash
    fails closed until a human checks the journal and removes it. -/
@[extern "tornado_private_replace"]
opaque replacePrivate (path : @& String) (expected : @& ByteArray)
    (contents : @& ByteArray) : IO Unit

/-- Remove only an unchanged protected inode, then sync the parent directory.
    A failed or ambiguous removal must not be taken as lock release. -/
@[extern "tornado_private_remove_exact"]
opaque removePrivateExact (path : @& String) (expected : @& ByteArray) : IO Unit

/-- Verify an existing directory by descriptor. Unlike ordinary trusted
    ancestors, a claim directory must be owned by this process, have exact
    mode 0700, and have no ACL grants to other principals. -/
@[extern "tornado_private_dir_check"]
opaque checkPrivateDirectory (path : @& String) : IO Unit

end Tornado.Runtime.ProtectedIO
