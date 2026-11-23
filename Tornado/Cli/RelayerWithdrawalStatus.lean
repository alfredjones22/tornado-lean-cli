import Lean
import Tornado.Domain.Catalog
import Tornado.Domain.NoteIdentity
import Tornado.Crypto.Keccak
import Tornado.Protocol.Events
import Tornado.Protocol.RpcReceipt
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.ProtectedIO

/-!
Conservative Classic-relayer withdrawal reconciliation from exact pool events
and chain receipts. Relayer job claims are deliberately not treated as proof.
No transaction or proof is submitted by this module.
-/

namespace Tornado.Cli.RelayerWithdrawalStatus

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime

private def invalid : String := "This is not a supported Classic relayer withdrawal status file."

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
  | .ok value => value.getStr?.map some

private def hex (raw : String) (width : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw invalid
  let bytes ← parseHexBytes raw
  if bytes.size != width then throw invalid
  return bytes

private def address (raw : String) : Except String Nat := do
  let bytes ← hex raw 20
  let value := bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  if value == 0 then throw invalid
  return value

private def bytesNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def relayerUrlValid (raw : String) : Bool :=
  raw.startsWith "https://" && raw.endsWith "/" && raw.length <= 2048 &&
  let host := String.ofList ((raw.toList.drop 8).take (raw.length - 9))
  !host.isEmpty && host.toList.all (fun c =>
    c.isAlphanum || c == '.' || c == '-' || c == ':' || c == '[' || c == ']')

private def jobIdValid (raw : String) : Bool :=
  !raw.isEmpty && raw.length <= 256 && raw.toList.all (fun c =>
    c.isAlphanum || c == '_' || c == '-')

structure Record where
  chainId : ChainId
  pool : Nat
  nullifierHash : ByteArray
  recipient : Nat
  rewardAccount : Nat
  fee : Nat
  relayerUrl : String
  rpcUrl : String
  fromBlock : Option Nat
  jobId : Option String
  transactionHash : Option ByteArray
  raw : Json
  deriving Inhabited

/-- Parse the protected TypeScript record and bind its pool to an original
    Classic-relayer-compatible catalog entry on the selected chain. -/
def parseRecord (root : Json) : Except String Record := do
  let version ← (← field root "version").getNat?
  if version != 1 || (← string root "kind") != "relayer" then throw invalid
  let chainNumber ← (← field root "chainId").getNat?
  let some chainId := chainFromNat chainNumber | throw invalid
  let poolText ← string root "poolAddress"
  let pool ← address poolText
  let known := (poolsFor chainId).find? fun item =>
    item.classicRelayer && item.address.toLower == poolText.toLower
  let some _ := known | throw invalid
  let nullifierHash ← hex (← string root "nullifierHash") 32
  let recipient ← address (← string root "recipient")
  let rewardAccount ← address (← string root "rewardAccount")
  let fee ← JsonRpc.parseHexQuantity (← string root "fee")
  let relayerUrl ← string root "relayerUrl"
  if !relayerUrlValid relayerUrl then throw invalid
  let rpcUrl ← string root "rpcUrl"
  if !HttpTransport.validRpcUrl rpcUrl then
    throw "Relayer status requires HTTPS or an explicit loopback HTTP RPC."
  let fromBlock ← match ← optionalString root "fromBlock" with
    | none => pure none
    | some text => (JsonRpc.parseHexQuantity text).map some
  let jobId ← optionalString root "jobId"
  if jobId.any (fun value => !jobIdValid value) then throw invalid
  let transactionHash ← match ← optionalString root "transactionHash" with
    | none => pure none
    | some text => (hex text 32).map some
  let status ← string root "status"
  if !["unknown", "pending", "confirmed", "failed"].contains status then throw invalid
  if let some message ← optionalString root "message" then
    if message.length > 1000 then throw invalid
  return ⟨chainId, pool, nullifierHash, recipient, rewardAccount, fee,
    relayerUrl, rpcUrl, fromBlock, jobId, transactionHash, root⟩

structure Candidate where
  transactionHash : ByteArray
  blockHash : ByteArray
  blockNumber : Nat
  transactionIndex : Nat
  logIndex : Nat
  event : Events.Withdrawal
  deriving Inhabited

private def parseLog (record : Record) (fromBlock toBlock : Nat)
    (raw : Json) : Except String (Option Candidate) := do
  let blockNumber ← JsonRpc.parseHexQuantity (← string raw "blockNumber")
  let transactionIndex ← JsonRpc.parseHexQuantity (← string raw "transactionIndex")
  let logIndex ← JsonRpc.parseHexQuantity (← string raw "logIndex")
  if blockNumber < fromBlock || blockNumber > toBlock then throw invalid
  let blockHash ← hex (← string raw "blockHash") 32
  let transactionHash ← hex (← string raw "transactionHash") 32
  if (← address (← string raw "address")) != record.pool then throw invalid
  if let .ok removed := field raw "removed" then
    if (← removed.getBool?) then throw invalid
  let rawTopics ← (← field raw "topics").getArr?
  if rawTopics.size != 2 then throw invalid
  let mut topics := #[]
  for item in rawTopics do topics := topics.push (← hex (← item.getStr?) 32)
  let dataText ← string raw "data"
  if !dataText.startsWith "0x" then throw invalid
  let data ← parseHexBytes dataText
  let log : Events.Log := ⟨record.pool, topics, data⟩
  let event ← Events.decodeWithdrawal log
  if event.nullifierHash != record.nullifierHash then return none
  return some ⟨transactionHash, blockHash, blockNumber,
    transactionIndex, logIndex, event⟩

private def quantityText (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def addressText (value : Nat) : String := Id.run do
  let mut bytes := ByteArray.empty
  for index in [0:20] do
    bytes := bytes.push ((value / 256 ^ (19 - index) % 256).toUInt8)
  return "0x" ++ bytesToHex bytes

private def hashText (value : ByteArray) : String := "0x" ++ bytesToHex value

private def logParams (record : Record) (fromBlock toBlock : Nat) : Array Json :=
  #[Json.mkObj [
    ("address", toJson (addressText record.pool)),
    ("fromBlock", toJson (quantityText fromBlock)),
    ("toBlock", toJson (quantityText toBlock)),
    ("topics", toJson #[hashText Events.withdrawalTopic])]]

structure Observation where
  status : String := "unknown"
  transactionHash : Option ByteArray := none
  message : String := ""
  deriving Inhabited

private def uncertain (message : String) (hash : Option ByteArray := none) : Observation :=
  ⟨"unknown", hash, message⟩

private def expected (record : Record) : Events.ExpectedWithdrawal :=
  ⟨record.pool, record.recipient, record.nullifierHash,
    record.rewardAccount, record.fee⟩

private def verifyReceipt (record : Record) (hash : ByteArray)
    (candidate : Option Candidate)
    (fetch : JsonRpc.Method → Array Json → IO Json) : IO Observation := do
  try
    let result ← fetch .getTransactionReceipt #[toJson (hashText hash)]
    if result == .null then
      return uncertain "The chain receipt is not available yet; do not retry blindly." (some hash)
    let receipt ← fromExcept (RpcReceipt.parseReceipt result hash)
    if receipt.to != some record.pool || !receipt.success ||
        (record.fromBlock.any (· > receipt.blockNumber)) then
      return uncertain "The transaction receipt does not prove this pool withdrawal." (some hash)
    if let some event := candidate then
      if event.transactionHash != hash || event.blockHash != receipt.blockHash ||
          event.blockNumber != receipt.blockNumber ||
          event.transactionIndex != receipt.transactionIndex then
        return uncertain "The pool log and transaction receipt disagree." (some hash)
    if Events.hasWithdrawal receipt.logs (expected record) then
      return ⟨"confirmed", some hash, ""⟩
    return uncertain "The receipt has no matching pool Withdrawal event; inspect the note before retrying." (some hash)
  catch _ =>
    return uncertain "The chain receipt could not be checked; inspect the note before retrying." (some hash)

/-- Scan the complete recorded range in bounded RPC chunks. A non-exhaustive
    or ambiguous scan cannot confirm anything. -/
private def scan (record : Record) (head : Nat)
    (fetch : JsonRpc.Method → Array Json → IO Json) : IO (Option Candidate × Bool) := do
  let some start := record.fromBlock | return (none, true)
  if start > head then return (none, false)
  let mut fromBlock := start
  let mut found : Option Candidate := none
  let mut totalLogs := 0
  for _ in [0:1024] do
    if fromBlock > head then return (found, true)
    let toBlock := min (fromBlock + 999) head
    let result ← fetch .getLogs (logParams record fromBlock toBlock)
    let logs ← fromExcept result.getArr?
    if logs.size > 10000 then throw <| IO.userError "Pool Withdrawal scan returned too many logs."
    totalLogs := totalLogs + logs.size
    if totalLogs > 100000 then throw <| IO.userError "Pool Withdrawal scan exceeded its log budget."
    for raw in logs do
      let parsed ← fromExcept (parseLog record fromBlock toBlock raw)
      if let some candidate := parsed then
        if found.isSome then throw <| IO.userError "Multiple pool Withdrawals match this nullifier."
        found := some candidate
    fromBlock := toBlock + 1
  return (found, fromBlock > head)

def reconcileWith (raw : String)
    (fetch : JsonRpc.Method → Array Json → IO Json) : IO (String × String × UInt32) := do
  if raw.toUTF8.size > 1024 * 1024 then throw <| IO.userError invalid
  let root ← fromExcept (Json.parse raw)
  let record ← fromExcept (parseRecord root)
  let observation ← try
    let network ← fromExcept <| JsonRpc.parseHexQuantity
      (← fromExcept (← fetch .chainId #[]).getStr?)
    if network != chainNumber record.chainId then
      pure (uncertain "The chain RPC is on a different network.")
    else do
      let head ← fromExcept <| JsonRpc.parseHexQuantity
        (← fromExcept (← fetch .blockNumber #[]).getStr?)
      let mut candidate : Option Candidate := none
      let mut complete := true
      if record.fromBlock.isSome then
        let (found, scanned) ← scan record head fetch
        candidate := found
        complete := scanned
      if !complete then
        pure (uncertain "The pool Withdrawal scan was incomplete or the RPC is behind the recorded block.")
      else if let some found := candidate then
        if found.event.recipient != record.recipient ||
            found.event.relayer != record.rewardAccount ||
            found.event.fee != record.fee then
          pure (uncertain "This nullifier was withdrawn with a different recipient, relayer or fee."
            (some found.transactionHash))
        else verifyReceipt record found.transactionHash (some found) fetch
      else if let some hash := record.transactionHash then
        verifyReceipt record hash none fetch
      else
        pure (uncertain (if record.fromBlock.isNone then
          "No submission block or transaction hash was recorded; inspect the relayer and note before retrying."
          else "No matching pool Withdrawal event was found; absence is not proof that retrying is safe."))
  catch _ => pure (uncertain "The pool Withdrawal scan or chain RPC could not be completed; inspect the chain before retrying.")
  let next := root.setObjVal! "status" (toJson observation.status)
  let next := next.setObjVal! "message" (toJson observation.message)
  let next := match observation.transactionHash with
    | none => next
    | some hash => next.setObjVal! "transactionHash" (toJson (hashText hash))
  let output := "Status: " ++ observation.status ++ "\n" ++
    (record.jobId.map ("Relayer job: " ++ · ++ "\n") |>.getD "") ++
    (observation.transactionHash.map (fun hash =>
      "Transaction: " ++ hashText hash ++ "\n") |>.getD "") ++
    (if observation.message.isEmpty then "" else observation.message ++ "\n")
  return (next.compress ++ "\n", output,
    if observation.status == "confirmed" then 0 else 2)

private structure Options where
  statusFile : Option String := none
  rpc : Option String := none
  help : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with help := true }
  | "--status-file" :: value :: rest => parseOptions rest { options with statusFile := some value }
  | "--rpc" :: value :: rest => parseOptions rest { options with rpc := some value }
  | "--bundler-url" :: _ :: rest => parseOptions rest options
  | ["--status-file"] => .error "error: option '--status-file <path>' argument missing"
  | ["--rpc"] => .error "error: option '--rpc <url>' argument missing"
  | ["--bundler-url"] => .error "error: option '--bundler-url <url>' argument missing"
  | item :: rest =>
      if item.startsWith "--status-file=" then
        parseOptions rest { options with statusFile := some (String.ofList (item.toList.drop 14)) }
      else if item.startsWith "--rpc=" then
        parseOptions rest { options with rpc := some (String.ofList (item.toList.drop 6)) }
      else if item.startsWith "--bundler-url=" then parseOptions rest options
      else .error s!"error: unknown option '{item}'"

private def help : String :=
  "Usage: tornado withdraw status --status-file <path> [--rpc <HTTPS URL>]\n\n" ++
  "Reconcile a Classic relayer withdrawal from pool logs and chain receipts.\n"

def statusCommand (args : List String) : IO (String × UInt32) := do
  let options ← fromExcept (parseOptions args)
  if options.help then return (help, 0)
  let some file := options.statusFile
    | throw <| IO.userError "error: required option '--status-file <path>' not specified"
  let current ← IO.currentDir
  let absolute := if (System.FilePath.mk file).isAbsolute then file
    else (current / file).toString
  let bytes ← ProtectedIO.readPrivate absolute
  let some raw := String.fromUTF8? bytes
    | throw <| IO.userError "Private relayer status file is not UTF-8."
  let root ← fromExcept (Json.parse raw)
  let record ← fromExcept (parseRecord root)
  let rpc := options.rpc.getD record.rpcUrl
  let requestId ← IO.mkRef (1 : Nat)
  let fetch (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let id ← requestId.get
    requestId.set (id + 1)
    HttpTransport.call rpc id method params
  let (updated, output, code) ← reconcileWith raw fetch
  ProtectedIO.replacePrivate absolute bytes updated.toUTF8
  return (output, code)

end Tornado.Cli.RelayerWithdrawalStatus
