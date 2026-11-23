import Tornado.Cli.DepositMulti
import Tornado.Runtime.ProtectedTxSender

/-! Sequential multi-note deposit execution. Private backups are reduced to
public commitments before planning. Keys remain inside NativeSigner. Each
signed transaction hash is durable before exposure, and any uncertain result
stops the entire sequence with its journal and sender lock retained. -/

namespace Tornado.Cli.DepositMultiSend

open Lean Tornado.Domain Tornado.Protocol Tornado.Crypto Tornado.Runtime
open Tornado.Cli.DepositMulti

private def checked (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

private def addressNat (raw : String) : Except String Nat := do
  if !raw.startsWith "0x" then throw "Invalid catalog address."
  let bytes ← parseHexBytes raw
  if bytes.size != 20 then throw "Invalid catalog address."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def hex := ProtectedTxSender.hex
private def address := ProtectedTxSender.address

def journalBytes (items : Array Item) (chain : ChainId) (sender : Nat)
    (steps : Array DepositSend.Step) (statuses : Array String)
    (hashes : Array (Option ByteArray)) : Except String ByteArray := do
  if steps.isEmpty || steps.size > 300 || steps.size != statuses.size ||
      steps.size != hashes.size then throw "Invalid multi-deposit journal dimensions."
  let mut records := #[]
  for i in [0:steps.size] do
    let step := steps[i]!
    let status := statuses[i]!
    if !(["planned", "prepared", "submitted", "confirmed", "unknown", "reverted"].contains status) ||
        (status != "planned" && hashes[i]!.isNone) then
      throw "Invalid multi-deposit journal status."
    let mut fields := [("kind", toJson step.kind.text), ("label", toJson step.label),
      ("to", toJson (← address step.to)), ("status", toJson status)]
    if let some hash := hashes[i]! then
      if hash.size != 32 then throw "Invalid multi-deposit transaction hash."
      fields := fields ++ [("hash", toJson (hex hash))]
    if step.kind == .deposit then
      let selected := items.filter (fun item => item.commitment == step.commitment)
      if selected.size != 1 then throw "Deposit step has no unique selected note."
      let item := selected[0]!
      if (← addressNat item.pool.address) != step.pool || step.to != step.pool then
        throw "Deposit journal pool differs from the reviewed note."
      fields := fields ++ [("pool", toJson item.pool.address),
        ("commitment", toJson (hex item.commitment)),
        ("denomination", toJson item.pool.denomination),
        ("asset", toJson item.pool.asset.symbol)]
    records := records.push (Json.mkObj fields)
  return ((Json.mkObj [("version", toJson (1 : Nat)),
    ("kind", toJson ("deposit" : String)),
    ("chainId", toJson (chainNumber chain)),
    ("account", toJson (← address sender)),
    ("createdAt", toJson ("native-lean" : String)),
    ("steps", Json.arr records)]).compress ++ "\n").toUTF8

structure Effects where
  rpc : Nat → JsonRpc.Method → Array Json → IO Json
  createJournal : ByteArray → IO Unit
  replaceJournal : ByteArray → ByteArray → IO Unit
  sign : Rlp.Transaction1559 → IO (Nat × TypedTransaction.SignedTyped)
  approve : String → IO Unit
  waitFinality : RpcReceipt.Receipt → IO Unit

private def contractWord (effects : Effects) (id target : Nat)
    (data : ByteArray) : IO Nat := do
  let value ← effects.rpc id .call
    #[Json.mkObj [("to", toJson (← checked <| address target)),
      ("data", toJson (hex data))], toJson ("latest" : String)]
  let raw ← checked value.getStr?
  let bytes ← checked <| parseHexBytes raw
  if !raw.startsWith "0x" || bytes.size != 32 then
    throw <| IO.userError "Contract call did not return one uint256 word."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def allowanceData (sender spender : Nat) : Except String ByteArray := do
  return Abi.selector "allowance(address,address)" ++
    (← Abi.addressWord sender) ++ (← Abi.addressWord spender)

private def selectedItem (items : Array Item) (step : DepositSend.Step) :
    Except String Item := do
  let found := items.filter (fun item => item.commitment == step.commitment)
  if found.size != 1 then throw "Deposit call has no unique selected note."
  return found[0]!

private def recheckStep (effects : Effects) (items : Array Item)
    (sender : Nat) (step : DepositSend.Step) : IO Unit := do
  if step.kind != .deposit then return
  let item ← checked <| selectedItem items step
  let denomination ← contractWord effects 200 step.pool (Abi.selector "denomination()")
  if denomination != item.pool.amount then
    throw <| IO.userError "Pool denomination changed before signing."
  if let some tokenText := item.pool.asset.token then
    let token ← checked <| addressNat tokenText
    let balance ← contractWord effects 201 token
      (Abi.selector "balanceOf(address)" ++ (← checked <| Abi.addressWord sender))
    let allowance ← contractWord effects 202 token
      (← checked <| allowanceData sender step.pool)
    if balance < item.pool.amount || allowance < item.pool.amount then
      throw <| IO.userError "Token balance or allowance changed before deposit."

private def validateStepReceipt (effects : Effects) (sender : Nat)
    (step : DepositSend.Step) (receipt : RpcReceipt.Receipt) : IO Unit := do
  if step.kind == .deposit then
    let expected : Events.ExpectedDeposit := ⟨step.pool, step.commitment⟩
    if RpcReceipt.depositOutcome receipt receipt.transactionHash expected != .confirmed then
      throw <| IO.userError "Receipt does not contain the exact reviewed Deposit event."
  else
    let allowance ← contractWord effects 600 step.to
      (← checked <| allowanceData sender step.spender)
    if allowance != step.approvalAmount then
      throw <| IO.userError "Approval did not set the reviewed allowance."

/-- A failed durable write cannot send. A failed or uncertain send cannot
advance to another note. All approvals and deposits use fresh nonce/fee reads. -/
def executeWith (effects : Effects) (items : Array Item) (chain : ChainId)
    (sender : Nat) (readings : Readings)
    (bounds : ProtectedTxSender.Bounds := {}) : IO String := do
  let planned ← checked <| DepositMulti.plan items chain sender readings true
  if planned.mode != .sequential || planned.batches.size != 1 then
    throw <| IO.userError "Expected a sequential native deposit plan."
  let steps := planned.batches[0]!
  let statuses ← IO.mkRef (Array.replicate steps.size "planned")
  let hashes ← IO.mkRef (Array.replicate steps.size (none : Option ByteArray))
  let initial ← checked <| journalBytes items chain sender steps (← statuses.get) (← hashes.get)
  let journal ← IO.mkRef initial
  effects.createJournal initial
  let update (index : Nat) (status : String) (hash : ByteArray) : IO Unit := do
    let nextStatuses := (← statuses.get).set! index status
    let nextHashes := (← hashes.get).set! index (some hash)
    let next ← checked <| journalBytes items chain sender steps nextStatuses nextHashes
    let old ← journal.get
    effects.replaceJournal old next
    journal.set next
    statuses.set nextStatuses
    hashes.set nextHashes
  for index in [0:steps.size] do
    let step := steps[index]!
    let txEffects : ProtectedTxSender.Effects := {
      rpc := effects.rpc, sign := effects.sign,
      approve := fun text => effects.approve s!"Step {index + 1}/{steps.size}: {text}",
      revalidate := recheckStep effects items sender step,
      recordPrepared := fun _ signed => update index "prepared" signed.transactionHash,
      recordSubmitted := update index "submitted",
      recordConfirmed := fun receipt => update index "confirmed" receipt.transactionHash,
      recordUnknown := fun hash => do
        if (← statuses.get)[index]! != "reverted" then update index "unknown" hash,
      recordFailed := fun receipt => update index "reverted" receipt.transactionHash,
      validateReceipt := validateStepReceipt effects sender step,
      waitFinality := effects.waitFinality }
    let call : ProtectedTxSender.Call := ⟨step.to, step.data, step.value, step.label⟩
    let _ ← ProtectedTxSender.sendWith txEffects (chainNumber chain) sender call bounds
  return s!"Confirmed {items.size} deposit(s) in {steps.size} sequential transaction(s)."

private def absolutePath (path : String) : IO String := do
  let current ← IO.currentDir
  return if (System.FilePath.mk path).isAbsolute then path else (current / path).toString

/-- Live sequential adapter. Explicit experimental mode is selected by Main;
this function never treats a previous journal or claim as permission to retry. -/
def experimentalSend (notesFile keyFile rpc journalPath : String)
    (chain : ChainId) (yes : Bool := false) : IO String := do
  let keyPath ← absolutePath keyFile
  let sender ← NativeSigner.addressFromProtectedFile keyPath
  let senderText ← checked <| address sender
  let privateBytes ← ProtectedIO.readPrivate (← absolutePath notesFile)
  let some raw := String.fromUTF8? privateBytes
    | throw <| IO.userError "Private note backup is not UTF-8."
  let items ← checked <| DepositMulti.publicItems raw chain
  let readings ← DepositMulti.liveReadings rpc items chain sender
  let _ ← checked <| DepositMulti.plan items chain sender readings true
  let journalPath ← absolutePath journalPath
  let keyDirectory := String.intercalate "/" (keyPath.splitOn "/").dropLast
  if keyDirectory.isEmpty then throw <| IO.userError "Key file has no safe parent directory."
  let senderLock := keyDirectory ++ "/.tornado-sender-" ++
    toString (chainNumber chain) ++ "-" ++ senderText.toLower ++ ".lock"
  let lockBytes := ((Json.mkObj [("version", toJson (1 : Nat)),
    ("kind", toJson ("sender-lock" : String)), ("sender", toJson senderText),
    ("journal", toJson journalPath)]).compress ++ "\n").toUTF8
  ProtectedIO.createPrivate senderLock lockBytes
  let created ← IO.mkRef (#[] : Array (String × ByteArray))
  try
    for item in items do
      let identity := s!"tornado-lean-cli/invoice/v1/{chainNumber chain}/{item.pool.address.toLower}/{(hex item.commitment).toLower}"
      let claimPath := keyDirectory ++ "/.tornado-invoice-" ++
        bytesToHex (keccak256 identity.toUTF8) ++ ".claim"
      let claim := ((Json.mkObj [("version", toJson (1 : Nat)),
        ("kind", toJson ("invoice-claim" : String)),
        ("chainId", toJson (chainNumber chain)), ("pool", toJson item.pool.address),
        ("commitment", toJson (hex item.commitment)),
        ("sender", toJson senderText), ("journal", toJson journalPath)]).compress ++ "\n").toUTF8
      ProtectedIO.createPrivate claimPath claim
      created.modify (·.push (claimPath, claim))
  catch error =>
    for (path, content) in (← created.get) do
      try ProtectedIO.removePrivateExact path content catch _ => pure ()
    try ProtectedIO.removePrivateExact senderLock lockBytes catch _ => pure ()
    throw error
  IO.println s!"Sender: {senderText}; {items.size} deposit(s); route: sequential EIP-1559."
  IO.println s!"Journal: {journalPath}"
  let effects : Effects := {
    rpc := HttpTransport.call rpc,
    createJournal := ProtectedIO.createPrivate journalPath,
    replaceJournal := ProtectedIO.replacePrivate journalPath,
    sign := NativeSigner.sign1559FromProtectedFile keyPath,
    waitFinality := ProtectedTxSender.waitReceiptDepth rpc,
    approve := fun text => do
      IO.println text
      if !yes then
        IO.println "Type SEND to sign and submit this one transaction:"
        let answer ← (← IO.getStdin).getLine
        if jsTrim answer != "SEND" then
          throw <| IO.userError "Deposit cancelled before signing." }
  let result ← try executeWith effects items chain sender readings
    catch _ =>
      throw <| IO.userError s!"Deposit sequence stopped. Inspect {journalPath}; sender lock remains at {senderLock}. Do not clear the lock or retry until every recorded hash is reconciled."
  ProtectedIO.removePrivateExact senderLock lockBytes
  return result

end Tornado.Cli.DepositMultiSend
