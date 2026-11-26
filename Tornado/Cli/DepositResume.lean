import Tornado.Cli.DepositMultiSend
import Tornado.Cli.DepositStatus

/-! Restart a sequential ETH plan from its original protected journal.
Recorded hashes are reconciled, never replaced. Only an unexposed suffix
can be signed, and every new hash is durable before network exposure. -/

namespace Tornado.Cli.DepositResume
open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Cli.DepositMulti

private def checked (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

private def hex := ProtectedTxSender.hex
private def address := ProtectedTxSender.address

structure State where
  steps : Array DepositSend.Step
  statuses : Array String
  hashes : Array (Option ByteArray)
  recordedPrefix : Nat

def validate (items : Array Item) (chain : ChainId) (sender : Nat)
    (raw : ByteArray) : Except String State := do
  if raw.size > 1024 * 1024 then throw "Resume journal exceeds one MiB."
  validateItems items chain
  if items.any (fun item => item.pool.asset.token.isSome) then
    throw "--resume currently supports sequential ETH deposits; token approval journals need separate reconciliation."
  let some text := String.fromUTF8? raw | throw "Resume journal is not UTF-8."
  let journal ← DepositStatus.parseJournal text
  let root ← Json.parse text
  if (← (← root.getObjVal? "createdAt").getStr?) != "native-lean" ||
      journal.chainId != chain || journal.account != sender ||
      journal.steps.size != items.size then
    throw "Resume journal differs from the original chain, sender or note count."
  let steps ← items.mapM depositStep
  let mut statuses := #[]
  let mut hashes := #[]
  let mut recordedCount := 0
  let mut planned := false
  for index in [0:steps.size] do
    let old := journal.steps[index]!
    let step := steps[index]!
    let isMatching := match old.expectedDeposit with
      | some expected => expected.pool == step.pool && expected.commitment == step.commitment
      | none => false
    if old.kind != .deposit || old.to != step.to || old.label != step.label ||
        !isMatching || old.status == .reverted then
      throw "Resume journal has a changed, reordered, unsupported or reverted deposit step."
    let hash ← old.hash.mapM parseHexBytes
    if old.status == .planned then
      if hash.isSome then throw "A planned resume step already contains a transaction hash."
      planned := true
    else
      if planned || hash.isNone then throw "Resume journal is not a recorded prefix followed by unexposed planned deposits."
      recordedCount := recordedCount + 1
    statuses := statuses.push old.status.text
    hashes := hashes.push hash
  return ⟨steps, statuses, hashes, recordedCount⟩

private def field (json : Json) (name : String) : IO Json := checked (json.getObjVal? name)
private def number (json : Json) : IO Nat := do
  checked <| JsonRpc.parseHexQuantity (← checked json.getStr?)
private def numField (json : Json) (name : String) : IO Nat := do number (← field json name)
private def bytesField (json : Json) (name : String) (width : Nat) : IO ByteArray := do
  let text ← checked <| (← field json name).getStr?
  let result ← checked <| parseHexBytes text
  if !text.startsWith "0x" || result.size != width then throw <| IO.userError "Malformed resume RPC evidence."
  return result
private def addrField (json : Json) (name : String) : IO Nat := do
  return (← bytesField json name 20).data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def registered (effects : DepositMultiSend.Effects) (step : DepositSend.Step) : IO Bool := do
  let json ← effects.rpc 701 .call #[Json.mkObj [
    ("to", toJson (← checked <| address step.pool)),
    ("data", toJson (hex (Abi.selector "commitments(bytes32)" ++ step.commitment)))],
    toJson ("latest" : String)]
  let text ← checked json.getStr?
  let bytes ← checked <| parseHexBytes text
  if !text.startsWith "0x" || bytes.size != 32 then throw <| IO.userError "Invalid commitment-registration response."
  let value := bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0
  if value > 1 then throw <| IO.userError "Invalid commitment-registration flag."
  return value == 1

private def requireUnfunded (effects : DepositMultiSend.Effects) (step : DepositSend.Step) : IO Unit := do
  if ← registered effects step then
    throw <| IO.userError "A planned commitment is already deposited without a matching recorded hash. Stop and reconcile it."

def resumeWith (effects : DepositMultiSend.Effects) (items : Array Item)
    (chain : ChainId) (sender : Nat) (original : ByteArray)
    (bounds : ProtectedTxSender.Bounds := { maxGas := DepositSend.maxTransactionGas })
    (broadcast : Bool := true) : IO String := do
  let state ← checked <| validate items chain sender original
  if (← number (← effects.rpc 700 .chainId #[])) != chainNumber chain then
    throw <| IO.userError "Resume RPC is on a different chain."
  let senderText ← checked <| address sender
  let mut previousNonce : Option Nat := none
  let mut nextStatuses := state.statuses
  for index in [0:state.recordedPrefix] do
    let step := state.steps[index]!
    let hash := state.hashes[index]!.get!
    let raw ← effects.rpc 710 .getTransactionReceipt #[toJson (hex hash)]
    if raw == .null then
      throw <| IO.userError s!"Step {index + 1} remains pending or unknown: {hex hash}. No replacement will be signed; run --resume again after reconciliation."
    let receipt ← checked <| RpcReceipt.parseReceipt raw hash
    if !receipt.success || receipt.origin != sender || receipt.to != some step.to then
      throw <| IO.userError "Recorded deposit reverted or its receipt identity differs; resume stopped."
    DepositMultiSend.validateStepReceipt effects sender step receipt
    let tx ← effects.rpc 711 .getTransactionByHash #[toJson (hex hash)]
    if tx == .null || (← bytesField tx "hash" 32) != hash ||
        (← addrField tx "from") != sender || (← addrField tx "to") != step.to ||
        (← numField tx "chainId") != chainNumber chain || (← numField tx "type") != 2 ||
        (← numField tx "value") != step.value ||
        (← bytesField tx "input" step.data.size) != step.data ||
        (← bytesField tx "blockHash" 32) != receipt.blockHash ||
        (← numField tx "blockNumber") != receipt.blockNumber ||
        (← numField tx "transactionIndex") != receipt.transactionIndex then
      throw <| IO.userError "Recorded transaction differs from the original reviewed deposit."
    let nonce ← numField tx "nonce"
    if let some prior := previousNonce then
      if nonce != prior + 1 then throw <| IO.userError "Recorded deposit nonces are not consecutive."
    previousNonce := some nonce
    let block ← effects.rpc 712 .getBlockByNumber
      #[toJson (ProtectedTxSender.quantity receipt.blockNumber), toJson false]
    if (← bytesField block "hash" 32) != receipt.blockHash ||
        (← numField block "number") != receipt.blockNumber ||
        (← number (← effects.rpc 713 .blockNumber #[])) < receipt.blockNumber ||
        !(← registered effects step) then
      throw <| IO.userError "Recorded deposit is no longer supported by the canonical block and commitment evidence."
    effects.waitFinality receipt
    nextStatuses := nextStatuses.set! index "confirmed"
    effects.progress s!"Step {index + 1}/{state.steps.size}: confirmed on chain; skipping."
  let pending ← number (← effects.rpc 714 .getTransactionCount #[toJson senderText, toJson ("pending" : String)])
  let latest ← number (← effects.rpc 715 .getTransactionCount #[toJson senderText, toJson ("latest" : String)])
  if pending != latest || previousNonce.any (fun nonce => latest != nonce + 1) then
    throw <| IO.userError "Sender has pending or unexpected nonce activity; reconcile before resuming."
  for index in [state.recordedPrefix:state.steps.size] do
    requireUnfunded effects state.steps[index]!
  if !broadcast then
    return s!"Resume preview: {state.recordedPrefix}/{items.size} deposits confirmed; {items.size - state.recordedPrefix} unexposed deposits remain. No journal, claim, or transaction was changed."
  let normalized ← checked <| DepositMultiSend.journalBytes items chain sender state.steps nextStatuses state.hashes
  -- The original bytes remain the CAS admission token, even if all statuses
  -- were already confirmed. Concurrent/stale resumptions cannot overwrite it.
  effects.replaceJournal original normalized
  let journal ← IO.mkRef normalized
  let statuses ← IO.mkRef nextStatuses
  let hashes ← IO.mkRef state.hashes
  let expectedNonce ← IO.mkRef latest
  let update (index : Nat) (status : String) (hash : ByteArray) : IO Unit := do
    let nextStatuses := (← statuses.get).set! index status
    let nextHashes := (← hashes.get).set! index (some hash)
    let next ← checked <| DepositMultiSend.journalBytes items chain sender state.steps nextStatuses nextHashes
    effects.replaceJournal (← journal.get) next
    journal.set next
    statuses.set nextStatuses
    hashes.set nextHashes
  for index in [state.recordedPrefix:state.steps.size] do
    let step := state.steps[index]!
    requireUnfunded effects step
    let txEffects : ProtectedTxSender.Effects := {
      rpc := effects.rpc
      sign := fun tx => do
        if tx.nonce != (← expectedNonce.get) then
          throw <| IO.userError "Sender nonce changed after resume admission; no new transaction was signed."
        let (actual, signed) ← effects.sign tx
        let _ ← checked <| DepositSend.certifySignedStep step tx signed
        return (actual, signed)
      approve := fun text => effects.approve s!"Step {index + 1}/{state.steps.size}: {text}"
      revalidate := do
        DepositMultiSend.recheckStep effects items sender step
        requireUnfunded effects step
      recordPrepared := fun _ signed => update index "prepared" signed.transactionHash
      recordSubmitted := update index "submitted"
      recordConfirmed := fun receipt => update index "confirmed" receipt.transactionHash
      recordUnknown := fun hash => do
        if (← statuses.get)[index]! != "reverted" then update index "unknown" hash
      recordFailed := fun receipt => update index "reverted" receipt.transactionHash
      validateReceipt := DepositMultiSend.validateStepReceipt effects sender step
      waitFinality := effects.waitFinality }
    let _ ← ProtectedTxSender.sendWith txEffects (chainNumber chain) sender
      ⟨step.to, step.data, step.value, step.label⟩ (DepositSend.stepBounds bounds step.value)
    expectedNonce.modify (· + 1)
  return s!"Confirmed {items.size} deposit(s); resumed {items.size - state.recordedPrefix} remaining deposit(s)."

private def absolutePath (path : String) : IO String := do
  let current ← IO.currentDir
  return if (System.FilePath.mk path).isAbsolute then path else (current / path).toString

/-- Existing reservations must belong to this exact journal. Missing claims
are admissible only for the validated, never-exposed suffix. All reservations
are retained after failure; success releases only the unchanged sender lock. -/
def command (notesFile keyFile rpc journalFile : String) (chain : ChainId)
    (broadcast : Bool) (nonInteractive : Bool := false) : IO String := do
  let keyPath ← absolutePath keyFile
  let journalPath ← absolutePath journalFile
  let sender ← NativeSigner.addressFromProtectedFile keyPath
  let senderText ← checked <| address sender
  let privateBytes ← ProtectedIO.readPrivate (← absolutePath notesFile)
  let some text := String.fromUTF8? privateBytes
    | throw <| IO.userError "Private note backup is not UTF-8."
  let items ← checked <| publicItems text chain
  let original ← ProtectedIO.readPrivate journalPath
  let state ← checked <| validate items chain sender original
  let some directory := (System.FilePath.mk keyPath).parent
    | throw <| IO.userError "Signing source has no reservation directory."
  let lock := (directory / s!".tornado-sender-{chainNumber chain}-{senderText.toLower}.lock").toString
  let lockBytes := ((Json.mkObj [("version", toJson (1 : Nat)),
    ("kind", toJson ("sender-lock" : String)), ("sender", toJson senderText),
    ("journal", toJson journalPath)]).compress ++ "\n").toUTF8
  let requireMatching (kind : DepositSend.DepositFileKind) (path : String)
      (bytes : ByteArray) (required : Bool) : IO Unit := do
    if ← (System.FilePath.mk path).pathExists then
      if (← ProtectedIO.readPrivate path) != bytes then
        throw <| IO.userError "An existing reservation belongs to a different journal or plan."
    else if required then
      throw <| IO.userError "A recorded deposit claim is missing. Keep the original signing directory and reconcile before resuming."
    else if broadcast then
      DepositSend.createProtectedFile kind path bytes
  -- A persistent sender claim plus journal CAS prevents replacement exposure;
  -- it does not pretend to be a process mutex.
  requireMatching .senderLock lock lockBytes false
  if (← ProtectedIO.readPrivate journalPath) != original then
    throw <| IO.userError "Journal changed during resume admission; rerun --resume to reconcile it."
  for index in [0:items.size] do
    let item := items[index]!
    let identity := s!"tornado-lean-cli/invoice/v1/{chainNumber chain}/{item.pool.address.toLower}/{(hex item.commitment).toLower}"
    let path := (directory / (".tornado-invoice-" ++ bytesToHex (keccak256 identity.toUTF8) ++ ".claim")).toString
    let bytes := ((Json.mkObj [("version", toJson (1 : Nat)),
      ("kind", toJson ("invoice-claim" : String)), ("chainId", toJson (chainNumber chain)),
      ("pool", toJson item.pool.address), ("commitment", toJson (hex item.commitment)),
      ("sender", toJson senderText), ("journal", toJson journalPath)]).compress ++ "\n").toUTF8
    requireMatching .invoiceClaim path bytes (index < state.recordedPrefix)
  IO.println s!"Resuming sequential ETH journal: {journalPath}"
  let effects : DepositMultiSend.Effects := {
    rpc := HttpTransport.call rpc
    createJournal := fun _ => throw <| IO.userError "Resume cannot create or overwrite a journal."
    replaceJournal := WithdrawalJournalProgram.replaceProtected journalPath
    sign := NativeSigner.sign1559FromProtectedFile keyPath
    waitFinality := ProtectedTxSender.confirmReceiptInclusion rpc
    progress := IO.println
    approve := fun review => do
      IO.println review
      if !nonInteractive then
        IO.println "Type SEND to sign and submit this remaining transaction:"
        if jsTrim (← (← IO.getStdin).getLine) != "SEND" then
          throw <| IO.userError "Resume cancelled before signing." }
  let result ← DepositMultiSend.withFailureContext journalPath lock
    (resumeWith effects items chain sender original
      { maxGas := DepositSend.maxTransactionGas } broadcast)
  if broadcast then ProtectedIO.removePrivateExact lock lockBytes
  return result

end Tornado.Cli.DepositResume
