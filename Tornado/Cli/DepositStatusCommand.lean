import Lean
import Tornado.Cli.DepositStatus
import Tornado.Cli.SmartAccountShow
import Tornado.Crypto.Keccak
import Tornado.Domain.NoteIdentity
import Tornado.Protocol.Abi
import Tornado.Protocol.Events
import Tornado.Protocol.RpcReceipt
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.ProtectedIO

/-!
Native `deposit status`: reconcile sequential and 7702 batch journals from
read-only chain evidence, then atomically compare-and-replace the original
protected journal. A transaction hash is never itself proof of a deposit.
-/

namespace Tornado.Cli.DepositStatusCommand

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime

private def invalid : String := "This is not a supported deposit status journal."

private def fromExcept (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def string (json : Json) (name : String) : Except String String := do
  (← field json name).getStr?

private def optionalString (json : Json) (name : String) : Except String (Option String) :=
  match field json name with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok item => item.getStr?.map some

private def hex (raw : String) (width : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw invalid
  let value ← parseHexBytes raw
  if value.size != width then throw invalid
  return value

private def address (raw : String) : Except String Nat := do
  let bytes ← hex raw 20
  let value := bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  if value == 0 then throw invalid
  return value

private def optionalHex (json : Json) (name : String) (width : Nat) :
    Except String (Option ByteArray) := do
  match ← optionalString json name with
  | none => return none
  | some raw => return some (← hex raw width)

private def optionalQuantity (json : Json) (name : String) : Except String (Option Nat) := do
  match ← optionalString json name with
  | none => return none
  | some raw => return some (← JsonRpc.parseHexQuantity raw)

private def put (json : Json) (name : String) (value : Json) : Json :=
  match json with
  | .obj entries => .obj (entries.insert name value)
  | other => other

private def setItems (root : Json) (name : String) (items : Array Json) : Json :=
  put root name (Json.arr items)

private def chainOf (root : Json) : Except String ChainId := do
  let version ← (← field root "version").getNat?
  if version != 1 then throw invalid
  let number ← (← field root "chainId").getNat?
  let some chain := chainFromNat number | throw invalid
  return chain

private def checkChain (chain : ChainId)
    (fetch : JsonRpc.Method → Array Json → IO Json) : IO Unit := do
  let result ← fetch .chainId #[]
  let actual ← fromExcept <| JsonRpc.parseHexQuantity (← fromExcept result.getStr?)
  if actual != chainNumber chain then
    throw <| IO.userError "The RPC endpoint is on a different network."

private def receiptOf (fetch : JsonRpc.Method → Array Json → IO Json)
    (hashText : String) : IO (Option RpcReceipt.Receipt) := do
  let expected ← fromExcept (hex hashText 32)
  try
    let result ← fetch .getTransactionReceipt #[toJson hashText]
    if result == .null then return none
    return (RpcReceipt.parseReceipt result expected).toOption
  catch _ => return none

private def updateSequential (raw : String) (root : Json)
    (fetch : JsonRpc.Method → Array Json → IO Json) : IO (Json × String) := do
  let journal ← fromExcept (DepositStatus.parseJournal raw)
  checkChain journal.chainId fetch
  let rawSteps ← fromExcept <| (← fromExcept (field root "steps")).getArr?
  let mut updated := #[]
  let mut lines := []
  for index in [0:journal.steps.size] do
    let step := journal.steps[index]!
    let receipt ← match step.hash with
      | none => pure none
      | some hash => receiptOf fetch hash
    let status := DepositStatus.classify journal step receipt
    updated := updated.push (put rawSteps[index]! "status" (toJson status.text))
    lines := lines ++ [s!"{index + 1}. {status.text}\t{step.label}{step.hash.map ("\t" ++ ·) |>.getD ""}"]
  return (setItems root "steps" updated,
    String.intercalate "\n" lines ++ "\n")

structure Batch where
  status : String
  deposits : List Events.ExpectedDeposit
  userOpHash : Option ByteArray
  transactionHash : Option ByteArray
  nonce : Option Nat
  fromBlock : Option Nat
  raw : Json
  deriving Inhabited

structure BatchJournal where
  chainId : ChainId
  sender : Nat
  entryPoint : Nat
  rpcUrl : String
  bundlerUrl : String
  batches : Array Batch
  deriving Inhabited

private def parseDeposit (chain : ChainId) (item : Json) : Except String Events.ExpectedDeposit := do
  let poolAddress ← address (← string item "pool")
  let commitment ← hex (← string item "commitment") 32
  let denomination ← string item "denomination"
  let asset ← string item "asset"
  let some pool := poolFor chain denomination asset | throw invalid
  if (← address pool.address) != poolAddress then throw invalid
  return ⟨poolAddress, commitment⟩

private def parseBatch (chain : ChainId) (json : Json) : Except String Batch := do
  let status ← string json "status"
  if !["planned", "prepared", "submitted", "pending", "confirmed",
      "failed", "rejected", "unknown"].contains status then throw invalid
  let deposits ← (← field json "deposits").getArr?
  if deposits.isEmpty || deposits.size > 12 then throw invalid
  let mut expected := []
  for item in deposits do
    expected := expected ++ [← parseDeposit chain item]
  let userOpHash ← optionalHex json "userOpHash" 32
  let transactionHash ← optionalHex json "transactionHash" 32
  let nonce ← optionalQuantity json "nonce"
  let fromBlock ← optionalQuantity json "fromBlock"
  return ⟨status, expected, userOpHash, transactionHash, nonce, fromBlock, json⟩

def parseBatchJournal (root : Json) : Except String BatchJournal := do
  if (← string root "kind") != "deposit-7702-batch" then throw invalid
  let chain ← chainOf root
  let sender ← address (← string root "sender")
  let entryPoint ← address (← string root "entryPointAddress")
  if entryPoint != (← address SmartAccountShow.entryPoint) then throw invalid
  let _ ← address (← string root "implementation")
  let rpcUrl ← string root "rpcUrl"
  let bundlerUrl ← string root "bundlerUrl"
  let _ ← string root "createdAt"
  let entries ← (← field root "batches").getArr?
  if entries.isEmpty || entries.size > 300 then throw invalid
  let mut batches := #[]
  for entry in entries do
    batches := batches.push (← parseBatch chain entry)
  return ⟨chain, sender, entryPoint, rpcUrl, bundlerUrl, batches⟩

private def hashText (bytes : ByteArray) : String := "0x" ++ bytesToHex bytes

private def addressText (value : Nat) : String :=
  match Abi.addressWord value with
  | .ok word => "0x" ++ bytesToHex (word.extract 12 32)
  | .error _ => "0x"

private def quantityText (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

/-- A log is only a transaction-location hint. Later receipt reconciliation
    still requires the exact EntryPoint event and every Deposit event. -/
private def findLogHash (journal : BatchJournal) (batch : Batch)
    (fetch : JsonRpc.Method → Array Json → IO Json) : IO (Option ByteArray × Bool) := do
  let some userOpHash := batch.userOpHash | return (none, false)
  let some fromBlock := batch.fromBlock | return (none, false)
  try
    let filter := Json.mkObj [
      ("address", toJson (addressText journal.entryPoint)),
      ("fromBlock", toJson (quantityText fromBlock)),
      ("toBlock", toJson ("latest" : String)),
      ("topics", toJson #[hashText Events.userOperationTopic, hashText userOpHash])]
    let raw ← fetch .getLogs #[filter]
    let logs ← fromExcept raw.getArr?
    if logs.size > 1 then return (none, true)
    if logs.isEmpty then return (none, false)
    let log := logs[0]!
    let emitter ← fromExcept <| address (← fromExcept <| string log "address")
    let topics ← fromExcept <| (← fromExcept <| field log "topics").getArr?
    if emitter != journal.entryPoint || topics.size < 2 ||
        topics[0]! != toJson (hashText Events.userOperationTopic) ||
        topics[1]! != toJson (hashText userOpHash) then return (none, false)
    if let .ok (.bool true) := field log "removed" then return (none, false)
    let block ← fromExcept <| JsonRpc.parseHexQuantity (← fromExcept <| string log "blockNumber")
    if block < fromBlock then return (none, false)
    let txHash ← fromExcept <| hex (← fromExcept <| string log "transactionHash") 32
    return (some txHash, false)
  catch _ => return (none, false)

private def classifyBatch (journal : BatchJournal) (batch : Batch)
    (receipt : Option RpcReceipt.Receipt) : String :=
  match batch.userOpHash, batch.nonce, batch.transactionHash, receipt with
  | some userOpHash, some nonce, some transactionHash, some value =>
      let entry : Events.ExpectedEntry :=
        ⟨journal.entryPoint, userOpHash, journal.sender, 0, nonce⟩
      if !value.success &&
          Events.uniqueEntryResult value.logs entry != some false then "unknown"
      else match RpcReceipt.batchDepositOutcome value transactionHash entry batch.deposits none with
        | .confirmed => "confirmed"
        | .failed => "failed"
        | .unknown => "unknown"
  | _, _, _, _ => "unknown"

private def batchMessage (status : String) : Option String :=
  if status == "confirmed" then none
  else if status == "failed" then
    some "The UserOperation reverted. Delegation may still remain; inspect this account before retrying."
  else some "The chain receipt did not prove every reviewed Deposit event; inspect it before retrying."

private def updateBatchFields (batch : Batch) (status : String)
    (hash : Option ByteArray) (message : Option String) : Json :=
  let next := put batch.raw "status" (toJson status)
  let next := match hash with
    | none => next
    | some value => put next "transactionHash" (toJson (hashText value))
  put next "message" (message.map toJson |>.getD .null)

/-- One conservative batch pass. The bundler can only suggest a transaction
    hash; exact EntryPoint and pool events in the chain receipt confirm it. -/
private def updateBatch (journal : BatchJournal)
    (fetchChain fetchBundler : JsonRpc.Method → Array Json → IO Json) :
    IO (Array Json × String) := do
  let mut updated := #[]
  let mut lines := []
  let mut confirmed := 0
  for index in [0:journal.batches.size] do
    let batch := journal.batches[index]!
    let mut hash := batch.transactionHash
    if batch.userOpHash.isNone then
      let status := if batch.status == "planned" || batch.status == "rejected" then
        batch.status else "unknown"
      let message := if status == "unknown" then
        some "No batch hash was recorded. A signed 7702 authorization may still be circulating; inspect the account before retrying."
        else none
      updated := updated.push (updateBatchFields batch status hash message)
      lines := lines ++ [s!"{index + 1}. {status}" ++
        (message.map ("\n   " ++ ·) |>.getD "")]
      continue
    if hash.isNone then
      try
        let result ← fetchBundler .getUserOperationReceipt
          #[toJson (hashText batch.userOpHash.get!)]
        if result != .null then
          if let .ok (.str returnedHash) := field result "userOpHash" then
            if (hex returnedHash 32).toOption != batch.userOpHash then
              throw <| IO.userError "Bundler returned another UserOperation."
          let nested ← fromExcept <| field result "receipt"
          if let .ok candidate := optionalHex nested "transactionHash" 32 then
            hash := candidate
      catch _ => pure ()
    let mut ambiguousLogs := false
    if hash.isNone then
      let (found, ambiguous) ← findLogHash journal batch fetchChain
      hash := found
      ambiguousLogs := ambiguous
    if hash.isNone then
      let message := if ambiguousLogs then
        "Multiple matching EntryPoint logs; inspect chain manually."
        else "No verified chain receipt yet; do not resubmit this batch."
      let status := if batch.status == "rejected" then "rejected" else "unknown"
      updated := updated.push (updateBatchFields batch status hash (some message))
      lines := lines ++ [s!"{index + 1}. {status}\t{hashText batch.userOpHash.get!}\n   {message}"]
      continue
    let txHash := hash.get!
    let receipt ← receiptOf fetchChain (hashText txHash)
    let status := classifyBatch journal { batch with transactionHash := hash } receipt
    let message := if receipt.isNone then
      some "The chain receipt is not available yet." else batchMessage status
    if status == "confirmed" then confirmed := confirmed + 1
    updated := updated.push (updateBatchFields batch status hash message)
    lines := lines ++ [s!"{index + 1}. {status}\t{hashText batch.userOpHash.get!}" ++
      (message.map ("\n   " ++ ·) |>.getD "")]
  return (updated,
    s!"{confirmed}/{journal.batches.size} batch(es) confirmed\n" ++
      String.intercalate "\n" lines ++ "\n")

def reconcileWith (raw : String)
    (fetchChain fetchBundler : JsonRpc.Method → Array Json → IO Json) :
    IO (String × String) := do
  if raw.toUTF8.size > 1024 * 1024 then
    throw <| IO.userError "Private deposit journal exceeds one MiB."
  let root ← fromExcept (Json.parse raw)
  let kind ← fromExcept (string root "kind")
  let (updated, output) ← if kind == "deposit" then
      updateSequential raw root fetchChain
    else if kind == "deposit-7702-batch" then do
      let journal ← fromExcept (parseBatchJournal root)
      checkChain journal.chainId fetchChain
      let (batches, output) ← updateBatch journal fetchChain fetchBundler
      pure (setItems root "batches" batches, output)
    else throw <| IO.userError invalid
  return (updated.compress ++ "\n", output)

private structure Options where
  journal : Option String := none
  rpc : Option String := none
  bundlerUrl : Option String := none
  help : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with help := true }
  | "--journal" :: value :: rest => parseOptions rest { options with journal := some value }
  | "--rpc" :: value :: rest => parseOptions rest { options with rpc := some value }
  | "--bundler-url" :: value :: rest => parseOptions rest { options with bundlerUrl := some value }
  | ["--journal"] => .error "error: option '--journal <path>' argument missing"
  | ["--rpc"] => .error "error: option '--rpc <url>' argument missing"
  | ["--bundler-url"] => .error "error: option '--bundler-url <url>' argument missing"
  | item :: rest =>
      if item.startsWith "--journal=" then
        parseOptions rest { options with journal := some (String.ofList (item.toList.drop 10)) }
      else if item.startsWith "--rpc=" then
        parseOptions rest { options with rpc := some (String.ofList (item.toList.drop 6)) }
      else if item.startsWith "--bundler-url=" then
        parseOptions rest { options with bundlerUrl := some (String.ofList (item.toList.drop 14)) }
      else .error s!"error: unknown option '{item}'"

private def help : String :=
  "Usage: tornado deposit status --journal <path> [--rpc <url>] [--bundler-url <url>]\n\n" ++
  "Reconcile a protected sequential or 7702 deposit journal against chain receipts.\n"

/-- Live CLI adapter. The original bytes are the compare-and-replace expected
    value, so a concurrent writer cannot be silently overwritten. -/
def statusCommand (args : List String) : IO String := do
  let options ← fromExcept (parseOptions args)
  if options.help then return help
  let some file := options.journal
    | throw <| IO.userError "error: required option '--journal <path>' not specified"
  let current ← IO.currentDir
  let absolute := if (System.FilePath.mk file).isAbsolute then file
    else (current / file).toString
  let bytes ← ProtectedIO.readPrivate absolute
  let some raw := String.fromUTF8? bytes
    | throw <| IO.userError "Private deposit journal is not UTF-8."
  let root ← fromExcept (Json.parse raw)
  let kind ← fromExcept (string root "kind")
  let chain ← fromExcept (chainOf root)
  let (defaultChainRpc, defaultBundler) ← if kind == "deposit-7702-batch" then do
      let batch ← fromExcept (parseBatchJournal root)
      pure (batch.rpcUrl, batch.bundlerUrl)
    else if kind == "deposit" then pure (defaultRpc chain, "")
    else throw <| IO.userError invalid
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := if kind == "deposit-7702-batch" then
      options.rpc.getD defaultChainRpc
    else (options.rpc.orElse (fun _ => environmentRpc)).getD defaultChainRpc
  let bundler := options.bundlerUrl.getD defaultBundler
  let chainId ← IO.mkRef (1 : Nat)
  let bundlerId ← IO.mkRef (1 : Nat)
  let fetchChain (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let id ← chainId.get
    chainId.set (id + 1)
    HttpTransport.call rpc id method params
  let fetchBundler (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let id ← bundlerId.get
    bundlerId.set (id + 1)
    HttpTransport.call bundler id method params
  let (updated, output) ← reconcileWith raw fetchChain fetchBundler
  ProtectedIO.replacePrivate absolute bytes updated.toUTF8
  return output

end Tornado.Cli.DepositStatusCommand
