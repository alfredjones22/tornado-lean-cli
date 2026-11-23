# Native per-note claim scope

`Tornado/Runtime/NoteClaims.lean` adds permanent, exclusive claim files for
each nullifier hash **within one trusted local CLI instance root**. The root
must have pre-existing, current-user-owned `claims/` and `attempts/`
directories with exact mode `0700` and no ACL grants. A descriptor-based
native check rejects symlinks and verifies those properties before reads or
writes. This generic claim API is not the opaque status-file journal used by
connected experimental commands; those use `Cli/WithdrawalJournal.lean` and
the relayer journal. Its theorems must not be presented as a proof of those IO
adapters.

`startClaimed` validates the attempt ID, reviewed operation hash, and unique
selected nullifiers before writing anything. It creates one protected file per
nullifier with `O_EXCL`, mode `0600`, and file/directory `fsync` through the
reviewed `ProtectedIO` binding. Only after *all* selected claims are created
does it call `AttemptJournal.start`. Each canonical claim record binds the
nullifier, attempt ID, direct/batch kind, reviewed hash, and full ordered
selection. `loadClaimed`, `appendClaimed`, and `armClaimedSubmission` replay the
journal and recheck every claim before advancing it. The file name is the
lowercase nullifier hash without `0x`, so a duplicate across attempts within
the same instance loses the exclusive-create race. Claims are scoped by
nullifier alone; reuse across pools or chains is conservatively blocked.

There is **no atomic multi-file transaction**. If a batch crashes or conflicts
partway through claiming, some notes may remain permanently claimed even
though no journal exists. If journal creation then fails, all notes may be
claimed without a journal. The API stops with an error in both cases. It never
converts an existing claim, even one with the same attempt ID, into success;
the caller must investigate the files and chain state manually. Claims are not
automatically deleted after confirmation or an apparently failed send. This
favors prevention of duplicate spends over availability. This API has no
claim-release operation.

The native test covers direct and batch claims, replay, a partial batch,
unknown outcomes, missing journal/claim failures, rejection of directory
mode `0755`, and a two-process exclusive-create race. It does not prove OS
crash durability or test every
filesystem. `ProtectedIO` still trusts the local filesystem and OS. A user or
malware with the same account can delete or alter claims and journals; this
is not a tamper-evident store. Separate instance roots can also claim the
same note, and an application that bypasses these wrappers can use the lower
level `AttemptJournal` directly. Any integration of this generic API must use
one canonical instance root and only the claimed wrappers. The runnable
withdrawal routes instead share opaque per-note claims within their selected
status directory; changing directories can bypass that local coordination.

The claim's reviewed hash and nullifier are caller supplied. This module
does not prove that the actual signed operation or Groth16 proof uses them,
does not authenticate receipts or chain finality, and cannot decide whether
a note is unspent. Those bindings remain prerequisites for money-moving use.
