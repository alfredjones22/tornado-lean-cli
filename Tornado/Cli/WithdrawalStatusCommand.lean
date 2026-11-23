import Lean
import Tornado.Domain.Status
import Tornado.Crypto.Keccak
import Tornado.Protocol.RpcReceipt
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.ProtectedIO

/-!
One-note 4337 status reconciliation against exact chain receipt and event
evidence. This command does not sign or submit. Relayer and batch records are
separate formats handled by their respective status commands.
-/

namespace Tornado.Cli.WithdrawalStatusCommand

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime

structure Observation where
  status : WithdrawalState
  transactionHash : Option String := none
  message : Option String := none
  deriving Inhabited

private def fromExcept (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def hexBytes (raw : String) (width : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw "Invalid withdrawal status hex value."
  let bytes ← parseHexBytes raw
  if bytes.size != width then throw "Invalid withdrawal status hex width."
  return bytes

private def hexNat (raw : String) (width : Nat) : Except String Nat := do
  let bytes ← hexBytes raw width
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def expectedEntry (status : OneNoteStatus) : Except String Events.ExpectedEntry := do
  let entryPoint ← hexNat status.entryPointAddress 20
  let userOpHash ← hexBytes status.userOpHash 32
  let sender ← hexNat status.sender 20
  let paymaster ← hexNat status.paymaster 20
  let nonce ← JsonRpc.parseHexQuantity status.nonce
  return { entryPoint, userOpHash, sender, paymaster, nonce }

private def expectedWithdrawal (status : OneNoteStatus) :
    Except String Events.ExpectedWithdrawal := do
  let pool ← hexNat status.poolAddress 20
  let recipient ← hexNat status.recipient 20
  let nullifierHash ← hexBytes status.nullifierHash 32
  let relayer ← hexNat status.paymaster 20
  let fee ← JsonRpc.parseHexQuantity status.fee
  return { pool, recipient, nullifierHash, relayer, fee }

private def quantityHex (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def unknown (message : String) (hash : Option String := none) : Observation :=
  ⟨.unknown, hash, some message⟩

private def hexString (json : Json) (field : String) (width : Nat) :
    Except String ByteArray := do
  hexBytes (← (← json.getObjVal? field).getStr?) width

private def logTransaction (item : Json) (entry : Events.ExpectedEntry)
    (fromBlock : Nat) : Except String (Option String) := do
  if let .ok value := item.getObjVal? "removed" then
    if value != .null && (← value.getBool?) then return none
  let block ← JsonRpc.parseHexQuantity (← (← item.getObjVal? "blockNumber").getStr?)
  if block < fromBlock then return none
  let address ← hexNat (← (← item.getObjVal? "address").getStr?) 20
  let topics ← (← item.getObjVal? "topics").getArr?
  if topics.size > 4 then return none
  let topicBytes ← topics.mapM fun value => do
    hexBytes (← value.getStr?) 32
  let data ← hexBytes (← (← item.getObjVal? "data").getStr?) 128
  let decoded ← Events.decodeUserOperationEvent
    { address, topics := topicBytes, data }
  if address != entry.entryPoint || decoded.userOpHash != entry.userOpHash ||
      decoded.sender != entry.sender || decoded.paymaster != entry.paymaster ||
      decoded.nonce != entry.nonce then return none
  let hash ← hexString item "transactionHash" 32
  return some ("0x" ++ bytesToHex hash)

/-- A bounded EntryPoint log lookup is a fallback when the bundler no longer
    indexes the operation. It filters only by public operation hash. -/
private def searchChainLog (status : OneNoteStatus)
    (fetch : String → JsonRpc.Method → Array Json → IO Json)
    (rpc : String) (entry : Events.ExpectedEntry) : IO (Option String) := do
  let some start := status.fromBlock | return none
  let fromBlock ← fromExcept (JsonRpc.parseHexQuantity start)
  let params := #[Json.mkObj [
    ("address", toJson status.entryPointAddress),
    ("fromBlock", toJson (quantityHex fromBlock)),
    ("toBlock", toJson ("latest" : String)),
    ("topics", Json.arr #[toJson ("0x" ++ bytesToHex Events.userOperationTopic),
      toJson status.userOpHash])]]
  let result ← fetch rpc .getLogs params
  let logs ← fromExcept result.getArr?
  if logs.size > 4096 then return none
  let mut found : Option String := none
  for item in logs do
    let next ← fromExcept (logTransaction item entry fromBlock)
    if let some hash := next then
      if found.isSome then return none
      found := some hash
  return found

private def bundlerHint (status : OneNoteStatus)
    (fetch : String → JsonRpc.Method → Array Json → IO Json)
    (bundler : String) (entry : Events.ExpectedEntry) : IO (Option RpcReceipt.BundlerHint) := do
  let chain ← fetch bundler .chainId #[]
  let number ← fromExcept (JsonRpc.parseHexQuantity (← fromExcept chain.getStr?))
  if number != chainNumber status.chainId then return none
  let result ← fetch bundler .getUserOperationReceipt #[toJson status.userOpHash]
  let envelope := Json.mkObj [("jsonrpc", toJson ("2.0" : String)),
    ("id", toJson (1 : Nat)), ("result", result)]
  fromExcept (RpcReceipt.parseBundlerResponse envelope 1 entry)

/-- One observation. Malformed or conflicting evidence never becomes a
    definitive success/failure; the caller may retry this read later. -/
def inspectWith (status : OneNoteStatus) (rpc bundler : String)
    (fetch : String → JsonRpc.Method → Array Json → IO Json) : IO Observation := do
  let entry ← fromExcept (expectedEntry status)
  let withdrawal ← fromExcept (expectedWithdrawal status)
  let chain? ← try
      let value ← fetch rpc .chainId #[]
      pure (some (← fromExcept (JsonRpc.parseHexQuantity (← fromExcept value.getStr?))))
    catch _ => pure none
  if chain? != some (chainNumber status.chainId) then
    return unknown "The chain RPC could not be checked on the selected network."
  let hint? ← try bundlerHint status fetch bundler entry
    catch _ => pure none
  let hash? := hint?.map (fun hint => "0x" ++ bytesToHex hint.transactionHash)
  let transactionHash ← if hash?.isSome then pure hash?
    else if status.transactionHash.isSome then pure status.transactionHash
    else try searchChainLog status fetch rpc entry
      catch _ => pure none
  let some hash := transactionHash | do
    let known ← try
        let chain ← fetch bundler .chainId #[]
        let number ← fromExcept (JsonRpc.parseHexQuantity (← fromExcept chain.getStr?))
        if number != chainNumber status.chainId then pure false
        else pure ((← fetch bundler .getUserOperationByHash #[toJson status.userOpHash]) != .null)
      catch _ => pure false
    if known then return ⟨.pending, none, none⟩
    return unknown "No verified receipt yet. The operation may still land; do not resend it."
  let receipt? ← try some <$> fetch rpc .getTransactionReceipt #[toJson hash]
    catch _ => pure none
  let some rawReceipt := receipt?
    | return unknown "The chain receipt could not be checked." (some hash)
  if rawReceipt == .null then return ⟨.pending, some hash, none⟩
  let parsed ← match RpcReceipt.parseReceipt rawReceipt (← fromExcept (hexBytes hash 32)) with
    | .ok receipt => pure receipt
    | .error _ => return unknown "The transaction receipt is malformed or mismatched." (some hash)
  let outcome := RpcReceipt.directWithdrawalOutcome parsed parsed.transactionHash
    entry withdrawal hint?
  match outcome with
  | .confirmed => return ⟨.confirmed, some hash, none⟩
  | .failed => return ⟨.failed, some hash,
      some "Execution failed. Reconcile before considering another withdrawal."⟩
  | .unknown => return unknown "No exact EntryPoint and pool Withdrawal evidence." (some hash)

private structure Options where
  file : Option String := none
  rpc : Option String := none
  bundler : Option String := none
  help : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with help := true }
  | "--status-file" :: value :: rest => parseOptions rest { options with file := some value }
  | "--rpc" :: value :: rest => parseOptions rest { options with rpc := some value }
  | "--bundler-url" :: value :: rest => parseOptions rest { options with bundler := some value }
  | ["--status-file"] => .error "error: option '--status-file <path>' argument missing"
  | ["--rpc"] => .error "error: option '--rpc <url>' argument missing"
  | ["--bundler-url"] => .error "error: option '--bundler-url <url>' argument missing"
  | value :: rest =>
      if value.startsWith "--status-file=" then
        parseOptions rest { options with file := some (String.ofList (value.toList.drop 14)) }
      else if value.startsWith "--rpc=" then
        parseOptions rest { options with rpc := some (String.ofList (value.toList.drop 6)) }
      else if value.startsWith "--bundler-url=" then
        parseOptions rest { options with bundler := some (String.ofList (value.toList.drop 14)) }
      else .error s!"error: unknown option '{value}'"

private def commandHelp : String :=
  "Usage: tornado withdraw status --status-file <path> [--rpc <url>] [--bundler-url <url>]\n" ++
  "Check a one-note 4337 withdrawal against chain receipt and event evidence.\n"

private def stateText : WithdrawalState → String
  | .pending => "pending" | .confirmed => "confirmed" | .failed => "failed"
  | .unknown => "unknown" | .rejected => "rejected"

def render (aggregate : OneNoteStatus)
    (observation : Observation)
    (candidates : List (OneNoteStatus × Observation) := []) : String :=
  "Status: " ++ stateText observation.status ++ "\n" ++
  "UserOperation: " ++ aggregate.userOpHash ++ "\n" ++
  String.join ((candidates.zipIdx).map fun ((candidate, checked), index) =>
    s!"Candidate {index + 1}: {stateText checked.status}\t{candidate.userOpHash}\n") ++
  (observation.transactionHash.map ("Transaction: " ++ · ++ "\n")).getD "" ++
  (observation.message.map (· ++ "\n")).getD "" ++
  "Status file: reconciled.\n"

def inspectRecordWith (record : WithdrawalStatusRecord) (rpc bundler : String)
    (fetch : String → JsonRpc.Method → Array Json → IO Json) :
    IO (OneNoteStatus × Observation × List (OneNoteStatus × Observation)) := do
  let selected := record.candidates.getD [record.current]
  let checked ← selected.mapM fun candidate => do
    let observation ← inspectWith candidate rpc bundler fetch
    pure (candidate, observation)
  let updated : List OneNoteStatus := checked.map fun pair =>
    let candidate := pair.1
    let observation := pair.2
    { candidate with
      status := observation.status
      transactionHash := observation.transactionHash.orElse (fun _ => candidate.transactionHash)
      message := observation.message.map toJson }
  let some aggregate := aggregateCandidate updated
    | throw <| IO.userError "Withdrawal status file contains no candidate."
  let observation := checked.find? (fun (candidate, _) =>
      candidate.userOpHash.toLower == aggregate.userOpHash.toLower) |>.map (·.2)
    |>.getD { status := .unknown }
  let observation := if record.candidates.isNone &&
      record.current.status == .rejected &&
      observation.status != .confirmed && observation.status != .failed then
      { status := WithdrawalState.rejected,
        transactionHash := record.current.transactionHash,
        message := some "The recorded pre-acceptance rejection remains in force." }
    else observation
  return (aggregate, observation, if record.candidates.isSome then checked else [])

private def updateFields (json : Json) (status : OneNoteStatus)
    (observation : Observation) : Json := Id.run do
  let mut result := json.setObjVal! "userOpHash" (toJson status.userOpHash)
  result := result.setObjVal! "fee" (toJson status.fee)
  result := result.setObjVal! "status" (toJson (stateText observation.status))
  if let some hash := observation.transactionHash then
    result := result.setObjVal! "transactionHash" (toJson hash)
  result := result.setObjVal! "message" (observation.message.map toJson |>.getD .null)
  return result

/-- Preserve unknown journal fields while updating only observed candidates.
    This requires the originally parsed candidate order and hashes to agree. -/
def updatedJournalJson (original : Json) (record : WithdrawalStatusRecord)
    (aggregate : OneNoteStatus) (observation : Observation)
    (checked : List (OneNoteStatus × Observation)) : Except String Json := do
  let .obj _ := original | throw "Withdrawal status file is not an object."
  let mut next := updateFields original aggregate observation
  if record.candidates.isSome then
    let rawCandidates ← (← original.getObjVal? "candidates").getArr?
    if rawCandidates.size != checked.length then
      throw "Withdrawal candidate count changed before journal update."
    let mut rewritten := #[]
    for i in [0:rawCandidates.size] do
      let row := rawCandidates[i]!
      let (candidate, result) := checked[i]!
      let savedHash ← (← row.getObjVal? "userOpHash").getStr?
      if savedHash.toLower != candidate.userOpHash.toLower then
        throw "Withdrawal candidate order changed before journal update."
      rewritten := rewritten.push (updateFields row candidate result)
    next := next.setObjVal! "candidates" (Json.arr rewritten)
  return next

def statusCommand (args : List String) : IO (String × UInt32) := do
  let options ← fromExcept (parseOptions args)
  if options.help then return (commandHelp, 0)
  let some file := options.file
    | throw <| IO.userError "error: required option '--status-file <path>' not specified"
  let current ← IO.currentDir
  let absolute := if (System.FilePath.mk file).isAbsolute then file
    else (current / file).toString
  let bytes ← ProtectedIO.readPrivate absolute
  let some raw := String.fromUTF8? bytes
    | throw <| IO.userError "Private withdrawal status file is not UTF-8."
  let record ← fromExcept (decodeWithdrawalStatus raw)
  let rpc := (options.rpc.orElse (fun _ =>
    record.rpcUrl.bind (·.getStr?.toOption))).getD (defaultRpc record.current.chainId)
  let bundler := (options.bundler.orElse (fun _ =>
    record.bundlerUrl.bind (·.getStr?.toOption))).getD rpc
  let id ← IO.mkRef (1 : Nat)
  let fetch (url : String) (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let next ← id.get
    id.set (next + 1)
    HttpTransport.call url next method params
  let (aggregate, observation, checked) ← inspectRecordWith record rpc bundler fetch
  let original ← fromExcept (Json.parse raw)
  let updated ← fromExcept (updatedJournalJson original record aggregate observation checked)
  let changed := (updated.compress ++ "\n").toUTF8
  ProtectedIO.replacePrivate absolute bytes changed
  return (render aggregate observation checked,
    if observation.status == .confirmed then 0 else 2)

end Tornado.Cli.WithdrawalStatusCommand
