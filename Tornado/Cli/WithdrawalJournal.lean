import Tornado.Cli.WithdrawalSend
import Tornado.Cli.BatchWithdrawalStatus
import Tornado.Domain.Status
import Tornado.Runtime.ProtectedIO
import Tornado.Runtime.WithdrawalJournalProgram

/-! Protected permanent note reservations shared with the classic-relayer
route. Every mirror contains the entire candidate before signed bytes leave
the process. A partial write is deliberately retained and prevents a retry.
These files contain privacy-sensitive public associations and executable
signed payloads; protected I/O is required even though no note is stored. -/

namespace Tornado.Cli.WithdrawalJournal

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Cli.WithdrawalSend

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def eventJson (note : SponsoredWithdrawal.NoteProof) : Except String Json := do
  return Json.mkObj [
    ("poolAddress", toJson (← Bundler.address note.request.pool)),
    ("nullifierHash", toJson (Bundler.dataHex (← Abi.uintWord note.request.nullifierHash))),
    ("recipient", toJson (← Bundler.address note.request.recipient)),
    ("relayer", toJson ("0x" ++ bytesToHex ((← Abi.addressWord note.request.relayer).extract 12 32))),
    ("fee", toJson (Bundler.quantity note.request.fee))]

/-- Construct a status-compatible record from the exact reserved operation.
The encoded payload includes any final authorization; the operation hash
alone does not bind a separate EIP-7702 authorization. -/
def record (review : Review) (op : UserOperation) (hash bytes : ByteArray)
    (paths : Array String) (rpc bundler : String) : Except String Json := do
  let expected ← build review
  if paths.size != review.notes.size || paths.isEmpty ||
      paths.toList.eraseDups.length != paths.size ||
      !HttpTransport.validRpcUrl rpc || !HttpTransport.validRpcUrl bundler ||
      hash != (← userOperationHash review.notes[0]!.request.chainId Bundler.entryPoint op) ||
      hash != (← userOperationHash review.notes[0]!.request.chainId Bundler.entryPoint expected) ||
      op.signature.size != 65 || bytes.size > Bundler.maxOperationBytes then
    throw "Withdrawal reservation differs from the reviewed operation."
  let some text := String.fromUTF8? bytes | throw "Invalid reserved payload encoding."
  let payload ← Json.parse text
  if payload.compress != text then throw "Reserved payload is not canonical."
  let base ← Bundler.encodeOperation op
  let fields := ["sender", "nonce", "callData", "callGasLimit", "verificationGasLimit",
    "preVerificationGas", "maxFeePerGas", "maxPriorityFeePerGas", "signature", "factory",
    "factoryData", "paymaster", "paymasterVerificationGasLimit", "paymasterPostOpGasLimit",
    "paymasterData"]
  for key in fields do
    if (payload.getObjVal? key).toOption != (base.getObjVal? key).toOption then
      throw "Reserved payload differs from signed operation bytes."
  let hashText := Bundler.dataHex hash
  let first := review.notes[0]!
  let common := [
    ("version", toJson (1 : Nat)), ("chainId", toJson first.request.chainId),
    ("rpcUrl", toJson rpc), ("bundlerUrl", toJson bundler),
    ("userOpHash", toJson hashText),
    ("entryPointAddress", toJson (← Bundler.address Bundler.entryPoint)),
    ("sender", toJson (← Bundler.address op.sender)),
    ("paymaster", toJson (← Bundler.address first.request.relayer)),
    ("nonce", toJson (Bundler.quantity op.nonce)),
    ("fromBlock", toJson (Bundler.quantity review.fromBlock)),
    ("status", toJson ("unknown" : String)), ("phase", toJson ("reserved" : String)),
    ("releaseReservations", toJson false),
    ("signedPayloadHash", toJson (Bundler.dataHex (keccak256 bytes))),
    ("signedOperation", payload)]
  let result ← match review.mode with
    | .single .. => do
      let fields := [
        ("poolAddress", toJson (← Bundler.address first.request.pool)),
        ("recipient", toJson (← Bundler.address first.request.recipient)),
        ("fee", toJson (Bundler.quantity first.request.fee)),
        ("nullifierHash", toJson (Bundler.dataHex (← Abi.uintWord first.request.nullifierHash)))]
      let candidate := Json.mkObj (common ++ fields)
      pure <| Json.mkObj (common ++ fields ++ [
        ("kind", toJson ("one-note-4337" : String)),
        ("candidates", Json.arr #[candidate])])
    | .batch .. => do
      let events ← review.notes.mapM eventJson
      let candidate := Json.mkObj [
        ("userOpHash", toJson hashText), ("events", Json.arr events),
        ("status", toJson ("unknown" : String))]
      pure <| Json.mkObj (common ++ [
        ("kind", toJson ("batch-4337" : String)), ("events", Json.arr events),
        ("statusFiles", toJson paths), ("candidates", Json.arr #[candidate])])
  match review.mode with
  | .single .. => let _ ← decodeWithdrawalStatus result.compress
  | .batch .. => let _ ← BatchWithdrawalStatus.parseRecord result
  return result

structure Journal where
  paths : Array String
  current : IO.Ref (Option Json)
  reservedHash : IO.Ref (Option ByteArray)

def create (paths : Array String) : IO Journal := do
  if paths.isEmpty || paths.size > 12 || paths.toList.eraseDups.length != paths.size then
    throw <| IO.userError "Invalid withdrawal reservation paths."
  return { paths, current := ← IO.mkRef none, reservedHash := ← IO.mkRef none }

def reservationProgram (paths : Array String) (contents : ByteArray) :
    WithdrawalJournalProgram.Program :=
  paths.toList.map (fun path => .create path contents)

def transitionProgram (paths : Array String) (expected contents : ByteArray) :
    WithdrawalJournalProgram.Program :=
  paths.toList.map (fun path => .replace path expected contents)

/-- Actual reservation returns the original pure-record equality and the
complete interpreted acknowledgement before its public wrapper returns Unit. -/
structure Reserved (paths : Array String) (review : Review) (op : UserOperation)
    (hash bytes : ByteArray) (rpc bundler : String) where
  private mk ::
  value : Json
  recorded : record review op hash bytes paths rpc bundler = .ok value
  acknowledged : WithdrawalJournalProgram.Acknowledged (reservationProgram paths value.compress.toUTF8)

def reserveWith (effects : WithdrawalJournalProgram.Effects) (journal : Journal)
    (review : Review) (op : UserOperation) (hash bytes : ByteArray) (rpc bundler : String) :
    IO (Reserved journal.paths review op hash bytes rpc bundler) := do
  if (← journal.current.get).isSome then
    throw <| IO.userError "Withdrawal candidate was already reserved."
  match recorded : record review op hash bytes journal.paths rpc bundler with
  | .error message => throw <| IO.userError message
  | .ok value =>
    let report ← WithdrawalJournalProgram.runIO effects
      (reservationProgram journal.paths value.compress.toUTF8)
    let acknowledged ← try WithdrawalJournalProgram.requireSuccess report
      catch _ =>
        throw <| IO.userError "A note is already reserved or its protected status file could not be created. Reconcile existing status files before retrying."
    journal.reservedHash.set (some hash)
    journal.current.set (some value)
    return ⟨value, recorded, acknowledged⟩

def reserve (journal : Journal) (review : Review) (op : UserOperation)
    (hash bytes : ByteArray) (rpc bundler : String) : IO Unit := do
  let _ ← reserveWith WithdrawalJournalProgram.protectedEffects journal review op hash bytes rpc bundler
  pure ()

structure Marked (paths : Array String) (phase : String) where
  private mk ::
  before : Json
  after : Json
  updated : after = before.setObjVal! "phase" (toJson phase)
  acknowledged : WithdrawalJournalProgram.Acknowledged
    (transitionProgram paths before.compress.toUTF8 after.compress.toUTF8)

def markWith (effects : WithdrawalJournalProgram.Effects) (journal : Journal)
    (hash : ByteArray) (phase : String) : IO (Marked journal.paths phase) := do
  if !(phase == "exposed" || phase == "submitted" || phase == "unknown") ||
      (← journal.reservedHash.get) != some hash then
    throw <| IO.userError "Withdrawal journal transition differs from its reservation."
  let some old ← journal.current.get
    | throw <| IO.userError "Withdrawal was not durably reserved."
  let next := old.setObjVal! "phase" (toJson phase)
  let report ← WithdrawalJournalProgram.runIO effects
    (transitionProgram journal.paths old.compress.toUTF8 next.compress.toUTF8)
  let acknowledged ← WithdrawalJournalProgram.requireSuccess report
  journal.current.set (some next)
  return ⟨old, next, rfl, acknowledged⟩

def mark (journal : Journal) (hash : ByteArray) (phase : String) : IO Unit := do
  let _ ← markWith WithdrawalJournalProgram.protectedEffects journal hash phase
  pure ()

theorem reserved_exact_mirrors (paths : Array String) (review : Review) (op : UserOperation)
    (hash bytes : ByteArray) (rpc bundler : String)
    (reserved : Reserved paths review op hash bytes rpc bundler) :
    record review op hash bytes paths rpc bundler = .ok reserved.value ∧
    reserved.acknowledged.trace = paths.toList.map
      (fun path => ⟨.create path reserved.value.compress.toUTF8, .acknowledged⟩) := by
  exact ⟨reserved.recorded, by
    simpa only [reservationProgram, List.map_map, Function.comp_def] using
      WithdrawalJournalProgram.successful_trace _ _ reserved.acknowledged.executed⟩

theorem marked_exact_mirrors (paths : Array String) (phase : String) (marked : Marked paths phase) :
    marked.after = marked.before.setObjVal! "phase" (toJson phase) ∧
    marked.acknowledged.trace = paths.toList.map
      (fun path => ⟨.replace path marked.before.compress.toUTF8 marked.after.compress.toUTF8,
        .acknowledged⟩) := by
  exact ⟨marked.updated, by
    simpa only [transitionProgram, List.map_map, Function.comp_def] using
      WithdrawalJournalProgram.successful_trace _ _ marked.acknowledged.executed⟩

end Tornado.Cli.WithdrawalJournal

#print axioms Tornado.Cli.WithdrawalJournal.reserved_exact_mirrors
#print axioms Tornado.Cli.WithdrawalJournal.marked_exact_mirrors

namespace Tornado.Cli.WithdrawalJournal

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Cli.WithdrawalSend

/-- Under the explicit physical create contract, a returned reservation's
complete matching execution occupies every selected path with its full exact
record bytes, and preserves all earlier occupied content. -/
theorem reserved_complete_physical (paths : Array String) (review : Review)
    (op : UserOperation) (hash bytes : ByteArray) (rpc bundler : String)
    (reserved : Reserved paths review op hash bytes rpc bundler)
    (trace : List WithdrawalJournalProgram.Physical.Observation)
    (before after : WithdrawalJournalProgram.Physical.Store)
    (physical : WithdrawalJournalProgram.Physical.Executes
      (reservationProgram paths reserved.value.compress.toUTF8) trace before after false) :
    (∀ path, path ∈ paths.toList → after path = some reserved.value.compress.toUTF8.data) ∧
    (∀ path previous, before path = some previous → after path = some previous) ∧
    trace.map WithdrawalJournalProgram.Physical.Observation.visible = reserved.acknowledged.trace := by
  have mirrored := WithdrawalJournalProgram.Physical.complete_create_program paths.toList
    reserved.value.compress.toUTF8 trace before after physical
  refine ⟨mirrored.1, mirrored.2, ?_⟩
  have observed := WithdrawalJournalProgram.Physical.visible_trace _ _ _ _ _ physical
  rw [WithdrawalJournalProgram.successful_trace _ _ observed,
    WithdrawalJournalProgram.successful_trace _ _ reserved.acknowledged.executed]

/-- After a complete reservation, any later interrupted create/CAS-only
journal update keeps the claims occupied. Even partial/unreadable claims or
lost replies cannot be re-admitted through exclusive creation. -/
theorem reserved_then_crash_blocks_readmission (paths : Array String) (review : Review)
    (op : UserOperation) (hash bytes : ByteArray) (rpc bundler : String)
    (reserved : Reserved paths review op hash bytes rpc bundler)
    (trace : List WithdrawalJournalProgram.Physical.Observation)
    (before reservedStore crashStore : WithdrawalJournalProgram.Physical.Store)
    (physical : WithdrawalJournalProgram.Physical.Executes
      (reservationProgram paths reserved.value.compress.toUTF8) trace before reservedStore false)
    (update : WithdrawalJournalProgram.Program)
    (crash : WithdrawalJournalProgram.Physical.CrashPrefix update reservedStore crashStore)
    (path : String) (selected : path ∈ paths.toList) (retry : ByteArray) :
    WithdrawalJournalProgram.Physical.apply (.create path retry) crashStore =
      .error "Exclusive journal path is occupied." := by
  have occupied := (reserved_complete_physical paths review op hash bytes rpc bundler
    reserved trace before reservedStore physical).1 path selected
  apply WithdrawalJournalProgram.Physical.occupied_blocks_readmission
  apply WithdrawalJournalProgram.Physical.crash_prefix_never_deletes _ _ _ crash path
  simp [occupied]

end Tornado.Cli.WithdrawalJournal

#print axioms Tornado.Cli.WithdrawalJournal.reserved_complete_physical
#print axioms Tornado.Cli.WithdrawalJournal.reserved_then_crash_blocks_readmission
