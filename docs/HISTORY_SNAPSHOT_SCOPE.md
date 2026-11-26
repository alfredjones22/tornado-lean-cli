# Native history snapshots and pinned offline assets

`history`, `compliance report`, and withdrawal preparation can use `--assets-dir` pointing to an existing UI `dist/offline` directory. The native loader resolves only the selected pool's `history/` file from 29 compiled descriptors copied from the pinned CLI manifest. It accepts gzip or decompressed JSON, enforces the exact uncompressed length and SHA-256, and checks the network, pool, denomination, asset, registration and cursor. It parses contiguous deposits and bounded withdrawals, then recomputes the full MiMC deposit root. File-provided replacement hashes are never accepted. A missing file permits a full Saga/RPC rebuild; a malformed file that is present fails closed.

The repository bundles nine pinned Sepolia snapshots under
`assets/history/11155111/`, covering all supported Sepolia pools through block
12,086,232. Live sponsored and Classic-relayer withdrawals use
`<proving-assets-root>/assets` for history assets by default, with the runtime
root inferred from the executable when `--proving-assets-root` is omitted.
An explicit `--assets-dir` overrides that history-assets directory; it names
the directory containing `history/`, rather than the proving-assets root.
These files provide a historical starting point, not current balances or a
substitute for checking the remaining history and selected note.

Historical SDK snapshots omit log indices for many records. The native representation explicitly marks them unknown; it does not invent an index. Note-specific history and compliance evidence still resolve the exact decoded deposit or withdrawal through a full-pool block query and a successful matching transaction receipt. The resolved receipt supplies the real log index and block/transaction hashes before the command reports confirmation.

An optional `--history-cache-dir` names an existing private directory owned by the user with mode 0700 and no ACL grants. Native cache records contain public pool history only, never a note, preimage, mnemonic, or selected-note association. Records are split into canonical, immutable content-addressed chunks of at most 1 MiB. Protected exclusive creation writes and syncs each new chunk before a small canonical index is published. Replacing an existing index uses protected compare-and-replace; a stale or concurrent writer fails closed. A crash before the index replacement leaves only unreferenced chunks, while the previous index continues to identify the previous complete state.

Before accepting a native cache, synchronization recomputes its deposit root and rechecks its saved count, root, and block hash at that exact height through the configured RPC. A pinned offline snapshot gets the same count and root check. A checkpoint that disagrees is discarded, and history is rebuilt from the pinned asset or pool registration. Every accepted native cache drops its stored finality claim and replays the 7,200-block legacy overlap before fetching the remaining tail. A hash check of the captured head at the beginning and end rejects a reorganization during synchronization. The cache makes the RPC scan budget apply to the tail rather than the whole deployment history.

Some RPCs cannot serve historical state at a snapshot's height. A transport
failure or a well-formed RPC error while checking that old state or cached
block hash makes the checkpoint unusable. Synchronization prints a fixed
rebuild notice, tries the next available checkpoint, then falls back to Saga
or a bounded deployment-to-head log replay. It never accepts the unchecked
checkpoint. File authentication happens before this fallback: malformed or
tampered assets/cache, malformed checkpoint replies, a changed RPC chain, and
budget violations still fail closed. Required current-head count/root checks
and the final head-hash check remain mandatory. Rebuilding can take several
minutes, or fail if Saga is unavailable and deployment history exceeds the
2,000,000-block RPC scan window. An RPC that serves the authenticated
checkpoint's historical state avoids that full replay.

Bounds include 128 MiB per decoded pinned asset, 256 MiB total native cache chunks, 1 MiB per protected chunk/index, 1,000 records per chunk, 4,096 chunks, a 2^20-leaf deposit tree, and the existing one-million-withdrawal and history run budgets. These are deliberate resource bounds. Exceeding one rejects the operation with an error instead of accepting incomplete state.

The checks establish consistency with the pinned manifest and the configured RPC's same-block claims. They do not authenticate Ethereum consensus, endpoint completeness, finality, deployed contract identity, disk power-loss behavior, or the cryptographic hardness of SHA-256/MiMC. In particular, withdrawals do not contribute to the deposit Merkle root. A selected note still needs the separate exact-block spent check and receipt evidence; a local cache alone must never authorize a spend.

`history_snapshot_test` covers a real pinned public snapshot, damaged content and a wrong hash, native cache roundtrip, checkpoint revalidation and overlap replay, changed or unavailable checkpoint rebuild, unavailable cached block hashes, corrupted content-addressed chunks, and stale index CAS rejection. It also checks that unavailable-checkpoint handling cannot bypass tampered files, malformed replies, changed chains or required current-head validation, and that provider error text is not reflected. `scripts/check_history_snapshots.py` checks every compiled descriptor against the pinned source manifest and authenticates the nine explicitly named bundled Sepolia files with bounded gzip decoding, exact sizes, SHA-256, record counts and pool/schema identifiers. MiMC reconstruction remains a native Lean check. Existing history synchronization and exact-receipt report tests remain unchanged.
