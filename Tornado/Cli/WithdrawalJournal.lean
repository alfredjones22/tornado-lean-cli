import Tornado.Cli.WithdrawalSend
import Tornado.Cli.BatchWithdrawalStatus
import Tornado.Domain.Status
import Tornado.Runtime.ProtectedIO

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

def reserve (journal : Journal) (review : Review) (op : UserOperation)
    (hash bytes : ByteArray) (rpc bundler : String) : IO Unit := do
  if (← journal.current.get).isSome then
    throw <| IO.userError "Withdrawal candidate was already reserved."
  let value ← checked <| record review op hash bytes journal.paths rpc bundler
  let contents := value.compress.toUTF8
  for path in journal.paths do
    -- No cleanup on a partial claim: another process or a prior attempt may
    -- own the remaining path. No network exposure occurs before all succeed.
    try ProtectedIO.createPrivate path contents
    catch _ =>
      throw <| IO.userError "A note is already reserved or its protected status file could not be created. Reconcile existing status files before retrying."
  journal.reservedHash.set (some hash)
  journal.current.set (some value)

def mark (journal : Journal) (hash : ByteArray) (phase : String) : IO Unit := do
  if !(phase == "exposed" || phase == "submitted" || phase == "unknown") ||
      (← journal.reservedHash.get) != some hash then
    throw <| IO.userError "Withdrawal journal transition differs from its reservation."
  let some old ← journal.current.get
    | throw <| IO.userError "Withdrawal was not durably reserved."
  let next := old.setObjVal! "phase" (toJson phase)
  for path in journal.paths do
    ProtectedIO.replacePrivate path old.compress.toUTF8 next.compress.toUTF8
  journal.current.set (some next)

end Tornado.Cli.WithdrawalJournal
