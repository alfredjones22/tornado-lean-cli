import Tornado.Cli.RelayerSend
import Tornado.Runtime.ReservationAdmission
import Tornado.Cli.WithdrawalSession
import Tornado.Cli.WithdrawOne

/-!
Explicitly experimental native Classic relayer command adapter. Only the
separate Lean worker opens the note; this process handles public metadata,
history, reviewed fees and proof bytes. The prover uses variable-time
arithmetic and does not guarantee secret erasure. Tests inject network effects
and do not submit funded withdrawals.
-/

namespace Tornado.Cli.RelayerWithdraw

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire

structure Input where
  noteFile : String
  recipient : String
  workerPath : String
  provingRoot : String
  rpcUrl : String
  chainId : Nat := 1
  noteIndex : Option String := none
  assetsDir : Option String := none
  cacheDir : Option String := none
  statusDir : String := "."
  experimental : Bool := false
  retryRejected : Bool := false
  yes : Bool := false
  waitMs : Nat := 180000
  deriving Inhabited

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def absolute (path : String) : IO String := do
  let current ← IO.currentDir
  let source := System.FilePath.mk path
  let value := if source.isAbsolute then source else current / source
  -- Resolve textual dot segments before handing paths to the protected
  -- descriptor walker; symlink traversal still remains forbidden by C.
  let mut components : List String := []
  for component in value.toString.splitOn "/" do
    if component.isEmpty || component == "." then continue
    if component == ".." then components := components.dropLast
    else components := components ++ [component]
  return "/" ++ String.intercalate "/" components

private def recipientNumber (raw : String) : Except String Nat := do
  let normalized ← WithdrawOne.checkedRecipient raw
  return (← parseHexBytes normalized).data.foldl (fun n byte => n * 256 + byte.toNat) 0

/-- The same opaque keyed filename used by direct/batch 4337 is the local
    per-note exclusive claim, so switching routes does not bypass an attempt. -/
def statusPath (directory : String) (metadata : Metadata) : IO String := do
  let _ ← checked metadata.validate
  let base ← absolute directory
  let metadata_ ← (System.FilePath.mk base).symlinkMetadata
  if metadata_.type != .dir then
    throw <| IO.userError "Relayer status directory must already be a regular directory."
  return (System.FilePath.mk base / metadata.statusFileName).toString

def run (input : Input) : IO (String × UInt32) := do
  if !input.experimental then
    throw <| IO.userError "Experimental relayer withdrawal requires explicit --experimental-send."
  if input.retryRejected then
    throw <| IO.userError "--retry-rejected is not available for the Classic relayer route."
  if input.yes then
    throw <| IO.userError "Experimental relayer withdrawals require typed WITHDRAW approval; --yes is unavailable."
  if !HttpTransport.validRpcUrl input.rpcUrl || input.waitMs > 300000 then
    throw <| IO.userError "Invalid experimental relayer RPC or wait bound."
  let recipient ← checked <| recipientNumber input.recipient
  let worker ← absolute input.workerPath
  let noteFile ← absolute input.noteFile
  let provingRoot ← absolute input.provingRoot
  let metadata ← ProverWorkerClient.inspectPrototype worker noteFile input.chainId input.noteIndex
  let pool ← checked <| WithdrawalSession.resolvePool metadata
  if !supportsClassicRelayer pool then
    throw <| IO.userError "Classic relayers support only original Tornado pools; use the 4337 route for this denomination."
  let path ← statusPath input.statusDir metadata
  let _ ← ReservationAdmission.requireUnclaimed #[path]
  let session ← WithdrawalSession.inspectLive input.rpcUrl metadata input.assetsDir input.cacheDir
  let readonly ← RelayerSend.nativeEffects input.rpcUrl
  let quote ← RelayerSend.prepareWith readonly session.pool
  let request ← checked <| WithdrawalSession.requestFor session recipient
    quote.relayer.rewardAccount quote.amounts.fee
  if !metadata.matchesRequest request then
    throw <| IO.userError "Selected note metadata differs from its reviewed relayer request."
  let accepted ← ProverWorkerClient.runPrototype worker provingRoot noteFile input.noteIndex request
  let prepared ← checked <| RelayerSend.prepareProof quote request {
    requestHash := request.hash, proof := accepted.proofBytes, signals := accepted.signals }
  let prepared ← RelayerSend.refreshPreparedWith readonly prepared
  let journal ← RelayerSend.protectedJournal path
  let effects : RelayerSend.SubmissionEffects := {
    readonly,
    approve := fun review => do
      IO.println review
      IO.println s!"Status file: {path}"
      IO.println "Type WITHDRAW to authorize one relayer proof submission:"
      let answer ← (← IO.getStdin).getLine
      if jsTrim answer != "WITHDRAW" then
        throw <| IO.userError "Relayer withdrawal cancelled before proof exposure.",
    revalidate := fun current => do
      if current != request then
        throw <| IO.userError "Relayer public inputs changed after review."
      WithdrawalSession.revalidateLive input.rpcUrl session,
    reserve := journal.reserve,
    update := journal.update,
    post := fun url body => do
      if url != prepared.quote.relayer.url ++ "v1/tornadoWithdraw" || body != prepared.body then
        throw <| IO.userError "Relayer proof payload differs from the reserved review."
      HttpTransport.postHttps url body,
    sleepMs := fun ms => IO.sleep ms.toUInt32 }
  let result ← RelayerSend.submitWith effects prepared input.rpcUrl { waitMs := input.waitMs }
  return (result.output ++ s!"Status file: {path}\n", result.code)

end Tornado.Cli.RelayerWithdraw
