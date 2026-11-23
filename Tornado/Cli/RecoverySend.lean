import Tornado.Cli.SmartAccountRecover
import Tornado.Cli.SmartAccountStatus
import Tornado.Runtime.ProtectedTxSender
import Tornado.Runtime.NativeSigner

/-! Experimental owner-paid SimpleAccount recovery. The exact supported-asset
sweep is reloaded after approval and a protected journal records the signed
transaction before exposure. Keys remain in the native signer. Live sending
requires an explicit experimental mode and a typed recovery confirmation. -/

namespace Tornado.Cli.RecoverySend

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.SmartAccount Tornado.Cli.SmartAccountRecover

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def fail (message : String) : IO α := throw <| IO.userError message

/-- Reconstruct the supported sweep independently from the stored balance
list, rejecting extra calls or a plan for another owner/account/recipient. -/
def validateReview (review : Review) : Except String Unit := do
  let _ ← SmartAccountRecover.render review
  if review.account.address != (← Tornado.SmartAccount.Address.predict review.account.owner) then
    throw "Recovery destination differs from the locally predicted smart account."
  let expected ← planRecovery review.chainId review.account.owner
    review.account.address review.plan.recipient review.plan.balances
    review.plan.entryPointDeposit
  if review.plan.data != expected.data then
    throw "Recovery calldata differs from the supported-asset sweep."

def sameReview (review current : Review) : Bool :=
  review.chainId == current.chainId &&
  review.account.owner == current.account.owner &&
  review.account.address == current.account.address && current.account.deployed &&
  review.plan.owner == current.plan.owner &&
  review.plan.account == current.plan.account &&
  review.plan.recipient == current.plan.recipient &&
  review.plan.data == current.plan.data &&
  review.plan.balances == current.plan.balances &&
  review.plan.entryPointDeposit == current.plan.entryPointDeposit

/-- A public transaction candidate must send zero ETH directly to the
reviewed deployed account, with exactly the supported recovery calls. -/
def validateCandidate (review : Review) (tx : Rlp.Transaction1559) :
    Except String Unit := do
  validateReview review
  Rlp.validateTransaction tx
  if tx.chainId != chainNumber review.chainId ||
      tx.to != some review.plan.account || tx.value != 0 ||
      tx.data != review.plan.data || !tx.accessList.isEmpty || tx.gas == 0 then
    throw "Recovery transaction differs from the reviewed sweep."

structure Effects where
  rpc : Nat → JsonRpc.Method → Array Json → IO Json
  sign : Rlp.Transaction1559 → IO (Nat × TypedTransaction.SignedTyped)
  approve : String → IO Unit
  rereview : IO Review
  createJournal : ByteArray → IO Unit
  replaceJournal : ByteArray → ByteArray → IO Unit
  waitFinality : RpcReceipt.Receipt → IO Unit

/-- Testable recovery command composition. A failed prepared write prevents
broadcast; every later failure retains the signed hash and stops without a
replacement. The live adapter retains the sender lock after signing starts. -/
def executeWith (effects : Effects) (review : Review)
    (bounds : ProtectedTxSender.Bounds := {}) : IO ByteArray := do
  let _ ← checked <| validateReview review
  let journalRef ← IO.mkRef (none : Option SmartAccountStatus.Journal)
  let bytesRef ← IO.mkRef (none : Option ByteArray)
  let statusRef ← IO.mkRef SmartAccountStatus.Status.prepared
  let update (status : SmartAccountStatus.Status) (message : Option String := none) : IO Unit := do
    let some journal ← journalRef.get | fail "Recovery journal has not been prepared."
    let some prior ← bytesRef.get | fail "Recovery journal snapshot is missing."
    let next ← checked <| SmartAccountStatus.journalBytes journal status message
    effects.replaceJournal prior next
    bytesRef.set (some next)
    statusRef.set status
  let senderEffects : ProtectedTxSender.Effects := {
    rpc := effects.rpc
    sign := effects.sign
    approve := effects.approve
    revalidate := do
      let current ← effects.rereview
      let _ ← checked <| validateReview current
      unless sameReview review current do
        fail "Smart account balances, identity or recovery calls changed; review again."
    recordPrepared := fun tx signed => do
      let _ ← checked <| validateCandidate review tx
      let journal : SmartAccountStatus.Journal := {
        chainId := review.chainId, owner := review.plan.owner,
        account := review.plan.account, recipient := review.plan.recipient,
        transactionHash := signed.transactionHash,
        calldataHash := keccak256 review.plan.data, priorStatus := .prepared }
      let bytes ← checked <| SmartAccountStatus.journalBytes journal .prepared
      effects.createJournal bytes
      journalRef.set (some journal)
      bytesRef.set (some bytes)
      statusRef.set .prepared
    recordSubmitted := fun _ => update .submitted
    recordConfirmed := fun _ => update .confirmed
    recordFailed := fun _ => update .failed
    recordUnknown := fun _ => do
      unless (← statusRef.get) == .failed do
        update .unknown (some "Check the recorded hash and chain receipt before retrying.")
    validateReceipt := fun receipt => do
      if receipt.origin != review.plan.owner ||
          receipt.to != some review.plan.account || !receipt.success then
        fail "Recovery receipt differs from the owner-paid transaction."
    waitFinality := effects.waitFinality }
  let call : ProtectedTxSender.Call := {
    to := review.plan.account
    data := review.plan.data
    value := 0
    label := "Recover the reviewed smart-account assets" }
  ProtectedTxSender.sendWith senderEffects (chainNumber review.chainId)
    review.plan.owner call bounds

/-- A cancellation or failure before any signing attempt may release the
lock. Once the signer is entered, every failure conservatively retains it;
only exact successful confirmation permits release. -/
def withSenderLock (createLock removeLock : IO Unit)
    (run : IO Unit → IO α) : IO α := do
  createLock
  let signingStarted ← IO.mkRef false
  try
    let result ← run (signingStarted.set true)
    removeLock
    return result
  catch error =>
    if !(← signingStarted.get) then
      try removeLock catch _ => pure ()
    throw error

private structure Options where
  owner : Option String := none
  ownerKeyFile : Option String := none
  receiver : Option String := none
  chain : String := "1"
  rpc : Option String := none
  journal : Option String := none
  experimentalSend : Bool := false
  dryRun : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "--experimental-send" :: rest =>
    if options.experimentalSend then .error "Duplicate recovery send flag."
    else parseOptions rest { options with experimentalSend := true }
  | "--dry-run" :: rest => parseOptions rest { options with dryRun := true }
  | "--owner" :: value :: rest =>
    if options.owner.isSome then .error "Duplicate recovery owner option."
    else parseOptions rest { options with owner := some value }
  | "--owner-key-file" :: value :: rest =>
    if options.ownerKeyFile.isSome then .error "Duplicate recovery key option."
    else parseOptions rest { options with ownerKeyFile := some value }
  | "--receiver" :: value :: rest =>
    if options.receiver.isSome then .error "Duplicate recovery receiver option."
    else parseOptions rest { options with receiver := some value }
  | "--chain" :: value :: rest => parseOptions rest { options with chain := value }
  | "--rpc" :: value :: rest =>
    if options.rpc.isSome then .error "Duplicate recovery RPC option."
    else parseOptions rest { options with rpc := some value }
  | "--journal" :: value :: rest =>
    if options.journal.isSome then .error "Duplicate recovery journal option."
    else parseOptions rest { options with journal := some value }
  | ["--owner"] | ["--owner-key-file"] | ["--receiver"] | ["--chain"] |
      ["--rpc"] | ["--journal"] => .error "Recovery option is missing its value."
  | argument :: rest =>
    if argument.startsWith "--owner=" then
      parseOptions ("--owner" :: String.ofList (argument.toList.drop 8) :: rest) options
    else if argument.startsWith "--owner-key-file=" then
      parseOptions ("--owner-key-file" :: String.ofList (argument.toList.drop 17) :: rest) options
    else if argument.startsWith "--receiver=" then
      parseOptions ("--receiver" :: String.ofList (argument.toList.drop 11) :: rest) options
    else if argument.startsWith "--chain=" then
      parseOptions ("--chain" :: String.ofList (argument.toList.drop 8) :: rest) options
    else if argument.startsWith "--rpc=" then
      parseOptions ("--rpc" :: String.ofList (argument.toList.drop 6) :: rest) options
    else if argument.startsWith "--journal=" then
      parseOptions ("--journal" :: String.ofList (argument.toList.drop 10) :: rest) options
    else .error "Unknown recovery send option."

private def absolutePath (raw : String) : IO String := do
  if raw.isEmpty then fail "Recovery file path is empty."
  let current ← IO.currentDir
  return if (System.FilePath.mk raw).isAbsolute then raw else (current / raw).toString

private def help : String :=
  "Usage: tornado smart-account recover --owner-key-file <path> (--dry-run | --experimental-send --journal <new-path>) [options]\n\n" ++
  "Recover supported balances and EntryPoint deposits with an owner-paid transaction.\n" ++
  "  --owner <address>     Expected owner; address-only dry run is also supported\n" ++
  "  --receiver <address>  Recovery recipient (default: owner)\n" ++
  "  --chain <id>          Ethereum chain ID (default: 1)\n" ++
  "  --rpc <url>           HTTPS chain RPC URL\n" ++
  "Experimental sending requires typing RECOVER after the exact transaction review.\n"

/-- Experimental live adapter. It neither chooses an existing
journal for retry nor clears an uncertain prior sender lock. The account is
predicted locally and its identity and sweep balances are read again after
approval, before the protected signer can be entered. -/
def recoverCommand (args : List String) : IO String := do
  if args.contains "--help" || args.contains "-h" then return help
  if !args.contains "--experimental-send" then
    if !args.contains "--dry-run" then
      fail "Choose --dry-run or --experimental-send for recovery."
    return (← SmartAccountRecover.recoverCommand args)
  let options ← checked <| parseOptions args
  if options.dryRun || !options.experimentalSend then
    fail "Choose either --dry-run or --experimental-send for recovery."
  let some keyFile := options.ownerKeyFile
    | fail "Experimental recovery requires --owner-key-file."
  let some journalFile := options.journal
    | fail "Experimental recovery requires a new --journal path."
  let chain ← checked <| parseChainInput options.chain
  let keyPath ← absolutePath keyFile
  let journalPath ← absolutePath journalFile
  let _ ← (System.FilePath.mk keyPath).symlinkMetadata
  let owner ← NativeSigner.addressFromProtectedFile keyPath
  if let some raw := options.owner then
    if (← checked <| SmartAccountShow.parseOwner raw) != owner then
      fail "Owner key differs from the expected owner address."
  let recipient ← match options.receiver with
    | none => pure owner
    | some raw => checked <| SmartAccountShow.parseOwner raw
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD (defaultRpc chain)
  let requestId ← IO.mkRef (1 : Nat)
  let read (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let id ← requestId.get
    requestId.set (id + 1)
    HttpTransport.call rpc id method params
  let review ← SmartAccountRecover.inspectWith chain owner recipient read
  let _ ← checked <| validateReview review
  let reviewText ← checked <| SmartAccountRecover.render review
  let senderText ← checked <| ProtectedTxSender.address owner
  let keyDirectory := String.intercalate "/" (keyPath.splitOn "/").dropLast
  if keyDirectory.isEmpty then fail "Recovery key has no protected parent directory."
  let senderLock := keyDirectory ++ "/.tornado-sender-" ++
    toString (chainNumber chain) ++ "-" ++ senderText.toLower ++ ".lock"
  let lockBytes := ((Json.mkObj [
    ("version", toJson (1 : Nat)), ("kind", toJson ("sender-lock" : String)),
    ("sender", toJson senderText), ("journal", toJson journalPath),
    ("purpose", toJson ("smart-account-recovery" : String))]).compress ++ "\n").toUTF8
  let hash ← try
    withSenderLock (ProtectedIO.createPrivate senderLock lockBytes)
      (ProtectedIO.removePrivateExact senderLock lockBytes) fun signingStarted => do
      let effects : Effects := {
        rpc := HttpTransport.call rpc
        sign := fun tx => do
          signingStarted
          NativeSigner.sign1559FromProtectedFile keyPath tx
        approve := fun transactionReview => do
          IO.print <| reviewText.replace
            "Dry run complete. No recovery transaction was signed or submitted.\n" ""
          IO.println s!"Journal: {journalPath}"
          IO.println transactionReview
          IO.println "Type RECOVER to sign and submit this owner-paid recovery transaction:"
          let answer ← (← IO.getStdin).getLine
          if jsTrim answer != "RECOVER" then fail "Recovery cancelled before signing."
        rereview := SmartAccountRecover.inspectWith chain owner recipient read
        createJournal := ProtectedIO.createPrivate journalPath
        replaceJournal := ProtectedIO.replacePrivate journalPath
        waitFinality := ProtectedTxSender.waitReceiptDepth rpc }
      executeWith effects review
    catch _ =>
      fail s!"Recovery did not reach confirmed completion. Inspect {journalPath}; do not retry while sender lock {senderLock} exists."
  return s!"Confirmed: {ProtectedTxSender.hex hash}\nJournal: {journalPath}\n"

end Tornado.Cli.RecoverySend
