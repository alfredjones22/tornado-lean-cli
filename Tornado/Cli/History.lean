import Lean
import Tornado.Domain.DepositBackup
import Tornado.Domain.ChainInput
import Tornado.Protocol.SelectedPoolBootstrap
import Tornado.Protocol.RpcHistory
import Tornado.Protocol.RpcReceipt
import Tornado.Protocol.Abi
import Tornado.Runtime.HistorySync
import Tornado.Runtime.ProtectedIO

/-!
Read-only, note-specific `history` command. The note is read through the
protected-file OS boundary and its identifiers are computed locally. Public
pool history is reconstructed through the bounded Saga/RPC synchronizer; the
same configured RPC then supplies the selected block's `isSpent` claim and
full-pool exact-block logs, successful receipts, and block hashes. The only
RPC log filter is the public pool address and exact block: no commitment or
nullifier is placed in a log filter. `isSpent` necessarily discloses the
nullifier hash to the chosen RPC, as the pinned TypeScript command does.

This is provider-checked evidence, not Ethereum consensus verification.
`HistorySync` may accept omitted withdrawal logs if the RPC and Saga both
omit them; the exact-block `isSpent` check detects this for the selected note.
No private note or preimage is printed or persisted.
-/

namespace Tornado.Cli.History

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.Events Tornado.Protocol.HistoryReducer

private def fail (message : String) : IO α :=
  throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => fail message

private def quantityHex (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def exactHex (raw : String) (width : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw "Malformed selected-pool RPC hex."
  let bytes ← parseHexBytes raw
  if bytes.size != width then throw "Malformed selected-pool RPC hex."
  return bytes

private def fieldString (json : Json) (key : String) : Except String String := do
  (← json.getObjVal? key).getStr?

private def fieldQuantity (json : Json) (key : String) : Except String Nat := do
  JsonRpc.parseHexQuantity (← fieldString json key)

private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def addressHex (address : Nat) : String := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:20] do
    bytes := bytes.push (UInt8.ofNat ((address / 256 ^ (19 - i)) % 256))
  return "0x" ++ bytesToHex bytes

private structure Options where
  noteFile : Option String := none
  noteIndex : Option String := none
  out : Option String := none
  chain : String := "1"
  rpc : Option String := none
  assetsDir : Option String := none
  cacheDir : Option String := none
  showHelp : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with showHelp := true }
  | "--note-file" :: value :: rest =>
    parseOptions rest { options with noteFile := some value }
  | "--note-index" :: value :: rest =>
    parseOptions rest { options with noteIndex := some value }
  | "--out" :: value :: rest =>
    parseOptions rest { options with out := some value }
  | "--chain" :: value :: rest =>
    parseOptions rest { options with chain := value }
  | "--rpc" :: value :: rest =>
    parseOptions rest { options with rpc := some value }
  | "--assets-dir" :: value :: rest =>
    parseOptions rest { options with assetsDir := some value }
  | "--history-cache-dir" :: value :: rest =>
    parseOptions rest { options with cacheDir := some value }
  | ["--note-file"] | ["--note-index"] | ["--out"] | ["--chain"] | ["--rpc"] =>
    .error "History option is missing its value."
  | ["--assets-dir"] | ["--history-cache-dir"] =>
    .error "History option is missing its value."
  | argument :: rest =>
    if argument.startsWith "--note-file=" then
      parseOptions rest { options with noteFile := some (String.ofList (argument.toList.drop 12)) }
    else if argument.startsWith "--note-index=" then
      parseOptions rest { options with noteIndex := some (String.ofList (argument.toList.drop 13)) }
    else if argument.startsWith "--out=" then
      parseOptions rest { options with out := some (String.ofList (argument.toList.drop 6)) }
    else if argument.startsWith "--chain=" then
      parseOptions rest { options with chain := String.ofList (argument.toList.drop 8) }
    else if argument.startsWith "--rpc=" then
      parseOptions rest { options with rpc := some (String.ofList (argument.toList.drop 6)) }
    else if argument.startsWith "--assets-dir=" then
      parseOptions rest { options with assetsDir := some (String.ofList (argument.toList.drop 13)) }
    else if argument.startsWith "--history-cache-dir=" then
      parseOptions rest { options with cacheDir := some (String.ofList (argument.toList.drop 20)) }
    else .error s!"error: unknown option '{argument}'"

private def help : String :=
  "Usage: tornado history --note-file <path> [--note-index <n>] [--chain <id>] [--rpc <url>]\n\n" ++
  "Check one protected note against bounded selected-pool history and exact-block chain evidence.\n" ++
  "  --assets-dir <path>          Pinned offline assets containing history/\n" ++
  "  --history-cache-dir <path>   Existing private 0700 directory for verified pool snapshots\n"

private def reportHelp : String :=
  "Usage: tornado compliance report --note-file <path> --out <path> [--note-index <n>] [--chain <id>] [--rpc <url>]\n\n" ++
  "Write one selected note's redacted chain evidence to a new protected JSON file.\n" ++
  "  --assets-dir <path>          Pinned offline assets containing history/\n" ++
  "  --history-cache-dir <path>   Existing private 0700 directory for verified pool snapshots\n"

def selectNote (contents : String) (chain : ChainId)
    (noteIndex : Option String) : Except String BackupIdentity := do
  let all ← parseDepositBackup contents chain
  let position ← match noteIndex with
    | none =>
      if all.length != 1 then
        throw s!"This backup has {all.length} notes. Select one with --note-index (1-based)."
      pure 1
    | some raw =>
      if raw.isEmpty || !raw.toList.all Char.isDigit then
        throw "Note index must be a positive decimal integer."
      let some parsed := raw.toNat? | throw "Note index is too large."
      if parsed == 0 || parsed > all.length then
        throw "Note index is outside this backup."
      pure parsed
  return all[position - 1]!

private def readSelectedNote (path : String) (chain : ChainId)
    (index : Option String) : IO BackupIdentity := do
  let current ← IO.currentDir
  let absolute := if (System.FilePath.mk path).isAbsolute then path
    else (current / path).toString
  let bytes ← ProtectedIO.readPrivate absolute
  let some contents := String.fromUTF8? bytes
    | fail "Private note backup is not UTF-8."
  checked (selectNote contents chain index)

/-- RPC evidence uses an injected transport so offline fixtures exercise the
    same request construction and validation as the live command. -/
private structure RpcContext where
  transport : HistorySync.Transport
  nextId : IO.Ref Nat
  chainId : Nat
  pool : Nat
  head : Nat

private def rpcRaw (context : RpcContext) (method : JsonRpc.Method)
    (params : Array Json) : IO (Nat × String) := do
  let id ← context.nextId.get
  if id ≥ 10064 then fail "History evidence RPC request budget exceeded."
  context.nextId.set (id + 1)
  let raw ← try context.transport.rpc id method params
    catch _ => fail "History evidence RPC request failed."
  if raw.toUTF8.size > RpcHistory.maxRpcResponseBytes then
    fail "History evidence RPC response exceeds one MiB."
  return (id, raw)

private def rpcResult (context : RpcContext) (method : JsonRpc.Method)
    (params : Array Json) : IO Json := do
  let (id, raw) ← rpcRaw context method params
  checked (JsonRpc.parseResult id raw)

private def checkChain (context : RpcContext) : IO Unit := do
  let raw ← rpcResult context .chainId #[]
  let chain ← checked (JsonRpc.parseHexQuantity (← checked raw.getStr?))
  if chain != context.chainId then fail "History evidence RPC chain changed."

private structure BlockHeader where
  hash : ByteArray
  timestamp : Nat

private def blockHeader (context : RpcContext) (number : Nat) : IO BlockHeader := do
  let json ← rpcResult context .getBlockByNumber #[toJson (quantityHex number), toJson false]
  if json == .null then fail "History evidence block is unavailable."
  let reported ← checked (fieldQuantity json "number")
  let hash ← checked (exactHex (← checked (fieldString json "hash")) 32)
  let timestamp ← checked (fieldQuantity json "timestamp")
  if reported != number then fail "History evidence block number changed."
  return { hash, timestamp }

private def isSpent (context : RpcContext) (nullifierHash : ByteArray) : IO Bool := do
  if nullifierHash.size != 32 then fail "Invalid local nullifier hash."
  let data := "0x" ++ bytesToHex (Abi.selector "isSpent(bytes32)") ++ bytesToHex nullifierHash
  -- An untrusted RPC error may echo the calldata, so do not propagate its
  -- message: this calldata contains the selected note's nullifier hash.
  let result ← try
      rpcResult context .call #[Json.mkObj [
        ("to", toJson (addressHex context.pool)), ("data", toJson data)],
        toJson (quantityHex context.head)]
    catch _ => fail "Selected-pool spent query failed."
  let word ← checked (exactHex (← checked result.getStr?) 32)
  let value := wordNat word
  if value > 1 then fail "Pool isSpent returned a noncanonical bool."
  return value == 1

private structure LocatedLog where
  log : Log
  blockNumber : Nat
  logIndex : Nat
  transactionHash : ByteArray
  blockHash : ByteArray
  deriving Inhabited

private structure VerifiedEvent where
  located : LocatedLog
  sender : Nat
  timestamp : Nat

private def exactLogs (context : RpcContext) (registeredBlock block : Nat) :
    IO (Array LocatedLog) := do
  let selection : SagaHistory.Selection := {
    chainId := context.chainId, pool := context.pool,
    registeredBlock, lastSyncedBlock := context.head, head := context.head }
  let params ← checked (RpcHistory.requestParams selection block block)
  let (chainId, chainRaw) ← rpcRaw context .chainId #[]
  let (logsId, logsRaw) ← rpcRaw context .getLogs params
  let parsed ← checked (RpcHistory.parseRange selection block block
    chainId logsId chainRaw logsRaw)
  let rawLogs ← checked ((← checked (JsonRpc.parseResult logsId logsRaw)).getArr?)
  if parsed.events.size != rawLogs.size then fail "History evidence RPC log count changed."
  let mut located := #[]
  for index in [0:parsed.events.size] do
    let event := parsed.events[index]!
    let raw := rawLogs[index]!
    let transactionHash ← checked (exactHex (← checked (fieldString raw "transactionHash")) 32)
    let blockHash ← checked (exactHex (← checked (fieldString raw "blockHash")) 32)
    located := located.push {
      log := event.log, blockNumber := event.blockNumber, logIndex := event.logIndex,
      transactionHash, blockHash }
  return located

private def findDeposit (state : State) (commitment : ByteArray) :
    Except String DepositRecord := do
  let foundRows := state.deposits.filter (fun row => row.commitment == commitment)
  if foundRows.size != 1 then
    throw "No unique matching deposit was found in the selected pool history."
  return foundRows[0]!

private def findWithdrawal (state : State) (nullifierHash : ByteArray) :
    Except String (Option WithdrawalRecord) := do
  let foundRows := state.withdrawals.filter (fun row => row.nullifierHash == nullifierHash)
  if foundRows.size > 1 then throw "Duplicate selected-note withdrawal in pool history."
  return foundRows[0]?

private def sameDeposit (candidate : LocatedLog) (record : DepositRecord) : Bool :=
  candidate.blockNumber == record.blockNumber &&
    (!record.logIndexKnown || candidate.logIndex == record.logIndex) &&
    match decodeDeposit candidate.log with
    | .error _ => false
    | .ok decoded => decoded.commitment == record.commitment &&
        decoded.leafIndex == record.leafIndex && decoded.timestamp == record.timestamp

private def sameWithdrawal (candidate : LocatedLog) (record : WithdrawalRecord) : Bool :=
  candidate.blockNumber == record.blockNumber &&
    (!record.logIndexKnown || candidate.logIndex == record.logIndex) &&
    match decodeWithdrawal candidate.log with
    | .error _ => false
    | .ok decoded => decoded.nullifierHash == record.nullifierHash &&
        decoded.recipient == record.recipient && decoded.relayer == record.relayer &&
        decoded.fee == record.fee

private def uniqueMatch (logs : Array LocatedLog) (predicate : LocatedLog → Bool) :
    Except String LocatedLog := do
  let found := logs.filter predicate
  if found.size != 1 then
    throw "The selected pool event could not be uniquely resolved on chain."
  return found[0]!

/-- Check an exact-block log against a successful receipt. The pure receipt
    parser enforces transaction and block metadata on every receipt log; the
    local check below also binds the event's global log index and full bytes. -/
private def verifyReceipt (context : RpcContext) (candidate : LocatedLog) : IO VerifiedEvent := do
  let hashText := "0x" ++ bytesToHex candidate.transactionHash
  let json ← rpcResult context .getTransactionReceipt #[toJson hashText]
  if json == .null then fail "The selected pool event has no transaction receipt."
  let receipt ← checked (RpcReceipt.parseReceipt json candidate.transactionHash)
  if !receipt.success || receipt.blockNumber != candidate.blockNumber ||
      receipt.blockHash != candidate.blockHash then
    fail "The selected pool event has no matching successful receipt."
  let rawLogs ← checked ((← checked (json.getObjVal? "logs")).getArr?)
  let parsedLogs := receipt.logs.toArray
  if rawLogs.size != parsedLogs.size then fail "Receipt log count changed."
  let mut matched := 0
  for index in [0:rawLogs.size] do
    let logIndex ← checked (fieldQuantity rawLogs[index]! "logIndex")
    if logIndex == candidate.logIndex then
      let parsed := parsedLogs[index]!
      if parsed.address != candidate.log.address ||
          parsed.topics != candidate.log.topics || parsed.data != candidate.log.data then
        fail "The selected pool event differs from its receipt log."
      matched := matched + 1
  if matched != 1 then fail "The selected pool event is absent from its receipt."
  let block ← blockHeader context candidate.blockNumber
  if block.hash != candidate.blockHash then
    fail "The selected pool event block hash differs from its receipt."
  return { located := candidate, sender := receipt.origin, timestamp := block.timestamp }

private structure Report where
  pool : Pool
  commitment : String
  nullifierHash : String
  checkedBlock : Nat
  checkedHeader : BlockHeader
  spent : Bool
  deposit : VerifiedEvent
  withdrawal : Option VerifiedEvent
  history : HistorySync.Result

private def renderHistory (report : Report) : Except String String := do
  let base :=
    s!"Pool: {report.pool.denomination} {report.pool.asset.symbol} ({report.pool.address})\n" ++
    s!"Deposit: 0x{bytesToHex report.deposit.located.transactionHash} at block {report.deposit.located.blockNumber}\n" ++
    s!"Spent: {if report.spent then "yes" else "no"} at checked block {report.checkedBlock}\n"
  match report.withdrawal with
  | none => return base
  | some withdrawal =>
    let decoded ← decodeWithdrawal withdrawal.located.log
    return base ++ s!"Withdrawal: 0x{bytesToHex withdrawal.located.transactionHash} at block {withdrawal.located.blockNumber}\n" ++
      s!"Recipient: {addressHex decoded.recipient}\n"

/-- A complete pinned-pool sync with exact-block root/count and block identity
rechecked. Only this module may construct it; per-note evidence can share the
same checked public snapshot without accepting an arbitrary caller's state. -/
structure SyncedSelection where
  private mk ::
  pool : Pool
  history : HistorySync.Result
  capturedBlockHash : ByteArray

def syncPublic (transport : HistorySync.Transport) (selectedPool : Pool)
    (assetsDir cacheDir : Option String := none) : IO SyncedSelection := do
  let pool ← checked (SelectedPoolBootstrap.selected (chainNumber selectedPool.chainId) selectedPool)
  let prior ← checked (SelectedPoolBootstrap.freshState (chainNumber selectedPool.chainId) pool.address)
  let synced ← if assetsDir.isSome || cacheDir.isSome then
      HistorySync.syncSelectedPoolWithAssets transport prior assetsDir cacheDir
    else HistorySync.syncSelectedPool transport prior
  checked <| HistoryReducer.validateState synced.state
  if synced.state.chainId != prior.chainId || synced.state.pool != prior.pool ||
      synced.state.registeredBlock != prior.registeredBlock ||
      synced.state.lastSyncedBlock != synced.capturedHead ||
      synced.state.verifiedRoot.isNone then fail "Selected pool sync identity changed."
  let nextId ← IO.mkRef 10000
  let context : RpcContext := {
    transport, nextId, chainId := prior.chainId, pool := prior.pool, head := synced.capturedHead }
  checkChain context
  let header ← blockHeader context synced.capturedHead
  let claim (signature : String) : IO Nat := do
    let result ← rpcResult context .call #[Json.mkObj [
      ("to", toJson (addressHex prior.pool)),
      ("data", toJson ("0x" ++ bytesToHex (Abi.selector signature)))],
      toJson (quantityHex synced.capturedHead)]
    return wordNat (← checked <| exactHex (← checked result.getStr?) 32)
  if synced.state.verifiedRoot != some (← claim "getLastRoot()") ||
      synced.state.deposits.size != (← claim "nextIndex()") then
    fail "Selected history differs from the exact-block pool root or count."
  checkChain context
  if (← blockHeader context synced.capturedHead).hash != header.hash then
    fail "The chain changed during selected-pool synchronization."
  return ⟨selectedPool, synced, header.hash⟩

private def inspectSyncedReport (transport : HistorySync.Transport)
    (selected : SyncedSelection) (commitmentText nullifierText : String) : IO Report := do
  let selectedPool := selected.pool
  let synced := selected.history
  let prior := synced.state
  let commitment ← checked (exactHex commitmentText 32)
  let nullifierHash ← checked (exactHex nullifierText 32)
  let deposit ← checked (findDeposit synced.state commitment)
  let withdrawal ← checked (findWithdrawal synced.state nullifierHash)
  let nextId ← IO.mkRef 10000
  let context : RpcContext := { transport := transport, nextId := nextId, chainId := prior.chainId, pool := prior.pool, head := synced.capturedHead }
  checkChain context
  let checkedHeader ← blockHeader context synced.capturedHead
  if checkedHeader.hash != selected.capturedBlockHash then
    fail "The selected pool block changed before note verification."
  let spent ← isSpent context nullifierHash
  if spent != withdrawal.isSome then
    fail "Selected pool history and same-block spent status disagree."
  let depositLogs ← exactLogs context prior.registeredBlock deposit.blockNumber
  let depositLog ← checked (uniqueMatch depositLogs (sameDeposit · deposit))
  let depositEvidence ← verifyReceipt context depositLog
  let withdrawalLog ← match withdrawal with
    | none => pure none
    | some record => do
      let logs ← if record.blockNumber == deposit.blockNumber then pure depositLogs
        else exactLogs context prior.registeredBlock record.blockNumber
      let found ← checked (uniqueMatch logs (sameWithdrawal · record))
      let evidence ← verifyReceipt context found
      if found.blockNumber < depositLog.blockNumber || record.fee > selectedPool.amount then
        fail "Selected-note withdrawal evidence is inconsistent with the deposit."
      pure (some evidence)
  checkChain context
  let finalHeader ← blockHeader context synced.capturedHead
  if finalHeader.hash != checkedHeader.hash then
    fail "The chain changed during history verification."
  return {
    pool := selectedPool, commitment := commitmentText, nullifierHash := nullifierText
    checkedBlock := synced.capturedHead, checkedHeader, spent
    deposit := depositEvidence, withdrawal := withdrawalLog, history := synced }

private def inspectReport (transport : HistorySync.Transport) (note : BackupIdentity)
    (assetsDir cacheDir : Option String := none) : IO Report := do
  let selected ← syncPublic transport note.note.pool assetsDir cacheDir
  inspectSyncedReport transport selected note.publicIdentity.commitment
    note.publicIdentity.nullifierHash

/-- Public-only evidence for a selected withdrawal. This reuses the exact
receipt, block-hash, same-block spent and complete-history checks of `history`
without constructing or importing a secret-bearing backup in the parent. -/
structure PublicSelection where
  history : HistorySync.Result
  capturedBlockHash : ByteArray
  spentAtHead : Bool
  leafIndex : Nat

def inspectPublicFromSynced (transport : HistorySync.Transport)
    (selected : SyncedSelection) (commitment nullifierHash : ByteArray) : IO PublicSelection := do
  if commitment.size != 32 || nullifierHash.size != 32 then
    fail "Invalid selected public note identifiers."
  let report ← inspectSyncedReport transport selected ("0x" ++ bytesToHex commitment)
    ("0x" ++ bytesToHex nullifierHash)
  let deposit ← checked (decodeDeposit report.deposit.located.log)
  return {
    history := report.history, capturedBlockHash := report.checkedHeader.hash
    spentAtHead := report.spent, leafIndex := deposit.leafIndex }

def inspectPublic (transport : HistorySync.Transport) (pool : Pool)
    (commitment nullifierHash : ByteArray)
    (assetsDir cacheDir : Option String := none) : IO PublicSelection := do
  let selected ← syncPublic transport pool assetsDir cacheDir
  inspectPublicFromSynced transport selected commitment nullifierHash

def inspect (transport : HistorySync.Transport) (note : BackupIdentity)
    (assetsDir cacheDir : Option String := none) : IO String := do
  checked (renderHistory (← inspectReport transport note assetsDir cacheDir))

private def evidenceFields (value : VerifiedEvent) : List (String × Json) := [
  ("transactionHash", toJson ("0x" ++ bytesToHex value.located.transactionHash)),
  ("blockNumber", toJson (toString value.located.blockNumber)),
  ("blockHash", toJson ("0x" ++ bytesToHex value.located.blockHash)),
  ("timestamp", toJson (toString value.timestamp)),
  ("transactionSender", toJson (addressHex value.sender)),
  ("logIndex", toJson value.located.logIndex)]

private def reportJson (report : Report) : Except String Json := do
  let deposit ← decodeDeposit report.deposit.located.log
  let withdrawal ← match report.withdrawal with
    | none => pure Json.null
    | some evidence => do
      let decoded ← decodeWithdrawal evidence.located.log
      if decoded.fee > report.pool.amount then throw "Withdrawal fee exceeds pool denomination."
      pure <| Json.mkObj (evidenceFields evidence ++ [
        ("recipient", toJson (addressHex decoded.recipient)),
        ("relayer", toJson (addressHex decoded.relayer)),
        ("feeBaseUnits", toJson (toString decoded.fee)),
        ("poolPayoutBaseUnits", toJson (toString (report.pool.amount - decoded.fee)))])
  return Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("chainId", toJson (chainNumber report.pool.chainId)),
    ("pool", Json.mkObj [
      ("address", toJson report.pool.address),
      ("asset", toJson report.pool.asset.symbol),
      ("denomination", toJson report.pool.denomination),
      ("amountBaseUnits", toJson (toString report.pool.amount))]),
    ("commitment", toJson report.commitment),
    ("nullifierHash", if report.spent then toJson report.nullifierHash else Json.null),
    ("checked", Json.mkObj [
      ("blockNumber", toJson (toString report.checkedBlock)),
      ("blockHash", toJson ("0x" ++ bytesToHex report.checkedHeader.hash)),
      ("timestamp", toJson (toString report.checkedHeader.timestamp)),
      ("spent", toJson report.spent)]),
    ("deposit", Json.mkObj (evidenceFields report.deposit ++
      [("leafIndex", toJson deposit.leafIndex)])),
    ("withdrawal", withdrawal)]

/-- JSON serialization contains public evidence but withholds the unspent
    nullifier hash and all private note material. The caller must still store
    it in a protected file because it links the note owner to a deposit. -/
def inspectJson (transport : HistorySync.Transport) (note : BackupIdentity)
    (assetsDir cacheDir : Option String := none) : IO String := do
  let json ← checked (reportJson (← inspectReport transport note assetsDir cacheDir))
  return json.pretty ++ "\n"

/-- Native runnable command. The private backup is opened before network
    access; only one selected note is used, and no secret bytes are output. -/
def historyCommand (args : List String) : IO String := do
  let options ← checked (parseOptions args)
  if options.showHelp then return help
  if options.out.isSome then fail "error: unknown option '--out'"
  let some file := options.noteFile
    | fail "error: required option '--note-file <path>' not specified"
  let chain ← checked (parseChainInput options.chain)
  let note ← readSelectedNote file chain options.noteIndex
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD (defaultRpc chain)
  let transport ← checked (HistorySync.liveTransport (chainNumber chain) rpc)
  inspect transport note options.assetsDir options.cacheDir

/-- Write the verified per-note evidence only after the full network check
    succeeds. Exclusive mode-0600 creation refuses to replace an existing
    report; the output path itself is not derived from the secret note. -/
def complianceReportCommand (args : List String) : IO String := do
  let options ← checked (parseOptions args)
  if options.showHelp then return reportHelp
  let some file := options.noteFile
    | fail "error: required option '--note-file <path>' not specified"
  let some out := options.out
    | fail "error: required option '--out <path>' not specified"
  let chain ← checked (parseChainInput options.chain)
  let note ← readSelectedNote file chain options.noteIndex
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD (defaultRpc chain)
  let transport ← checked (HistorySync.liveTransport (chainNumber chain) rpc)
  let rendered ← inspectJson transport note options.assetsDir options.cacheDir
  let current ← IO.currentDir
  let absolute := if (System.FilePath.mk out).isAbsolute then out
    else (current / out).toString
  ProtectedIO.createPrivate absolute rendered.toUTF8
  return s!"Verified report written to {absolute} (mode 0600).\n"

end Tornado.Cli.History
