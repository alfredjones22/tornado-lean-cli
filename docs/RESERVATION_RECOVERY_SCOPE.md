# Reservation and restart guarantees

The sponsored withdrawal journal now executes the finite file program in
`Runtime/WithdrawalJournalProgram.lean`. Its private acknowledgement records
the exact ordered create/CAS commands that returned successfully. The actual
`WithdrawalJournal.reserveWith` receipt also retains the equality to the
record built from the reviewed operation, complete signed payload and selected
paths. Its public native wrapper returns only after every mirror is acknowledged.
Memory state is advanced after those acknowledgements, never after a partial
write. No reservation command deletes a claim.

The physical interpretation is an explicit assumption about protected file
operations, separate from the callback trace. It admits a completed write with
a lost reply, an interrupted create leaving arbitrary partial/unreadable bytes,
an atomic replacement visible before its reply, and blocking stale locks.
`reserved_complete_physical` establishes that every selected path holds the
exact record bytes after a complete reservation under this contract.
`reserved_then_crash_blocks_readmission` establishes that those paths remain
occupied after a modeled later interruption and reject a new exclusive create.
This is a conditional theorem about the runtime-used adapter, rather than
substitution of the separate `AttemptJournal` example.

Initial route admission uses the finite `ReservationAdmission` interpreter on
the same opaque per-note paths. Native queries use `symlinkMetadata`: only
ENOENT means absence; other errors stop admission, and symlinks or malformed,
partial and empty entries count as occupied. The sponsored and Classic relayer
commands call this guard before preparing a proof. JSON outcome fields never
grant permission to ignore a reservation. The observation is not a lock: two
concurrent starts can both observe absence and sign. Only a complete winning
exclusive reservation may proceed to executable exposure; the losing attempt
stops. Per-attempt driver proofs do not establish global uniqueness of signing.

Batch status repair validates every existing mirror and preserves the union of
known transaction hints and strongest exposure phase. `RepairPlan` checks the
serialized staged and completed records retain the original normalized
reservation, including signed payloads, candidates, note order and unknown
extension fields. The shared interpreter CASes every exact snapshot to an
in-progress record before committing the first mirror's completion marker.
A failed or lost reply reports incomplete persistence. A complete persistence
result means the observation was saved; it does not mean the withdrawal
succeeded. Transaction success still requires the separate exact receipt/event
checks. A failed sponsored execution can leave its sponsor spent.

The native relayer, sequential deposit, 7702 deposit and recovery journal
callbacks also use the shared single-file interpreter. Their existing lock and
claim cleanup policies are retained. These shared write certificates do not
constitute full command-level refinement proofs for those engines. In
particular, exact-removal permission, receipt truth, confirmation depth and
key-signer behavior remain separate obligations; an acknowledged write alone
does not justify releasing a lock or trying another candidate.

Offline tests enumerate before-write and completed-with-lost-reply failures.
A separate native test includes the unchanged protected-I/O C source with
test-only syscall cut points and terminates child processes during five real
create/replace boundaries. It checks partial claims, committed bytes, exclusive
route exclusion, stale sidecars and stale CAS expectations. The fault object
and its arming FFI are linked only into the test executable.

The assumptions exclude hostile same-user modification, manual deletion,
copied status/key directories, storage corruption and an OS/device that violates
the specified protection, atomicity or durability contract. Callback traces and
finite tests do not prove those OS guarantees or Ethereum consensus. See
[the storage boundary](STORAGE_BOUNDARY.md) and
[the security contracts](SECURITY_CONTRACTS.md).
