import Lean
import Tornado.Cli.SmartAccountShow
import Tornado.Domain.Catalog
import Tornado.Domain.NoteIdentity
import Tornado.Crypto.Keccak
import Tornado.Protocol.Events
import Tornado.Protocol.RpcReceipt
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.ProtectedIO

/-!
Reconciliation of duplicated batch-4337 withdrawal status files. Every mirror
is validated before writing. An in-progress marker in the authoritative first
record precedes mirror updates; protected per-file compare-and-replace keeps
all reservations and candidate hashes through partial writes or races.
-/

namespace Tornado.Cli.BatchWithdrawalStatus

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime

private def invalid : String := "This is not a supported batch withdrawal status file."

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

private def address (raw : String) (allowZero : Bool := false) : Except String Nat := do
  let bytes ← hex raw 20
  let value := bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  if !allowZero && value == 0 then throw invalid
  return value

private def hashText (bytes : ByteArray) : String := "0x" ++ bytesToHex bytes

private def addressText (value : Nat) : String := Id.run do
  let mut bytes := ByteArray.empty
  for index in [0:20] do
    bytes := bytes.push ((value / 256 ^ (19 - index) % 256).toUInt8)
  return "0x" ++ bytesToHex bytes

private def quantityText (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def statusFileShape (chainId : ChainId) (path : String) : Bool :=
  let namePrefix := s!"tornado-withdraw-{chainNumber chainId}-"
  let components := path.splitOn "/"
  let name := components.getLast!
  let label := (name.toList.drop namePrefix.length).take 64
  path.startsWith "/" && !components.isEmpty &&
    (components.drop 1).all (fun part => !part.isEmpty && part != "." && part != "..") &&
    name.startsWith namePrefix && name.endsWith ".json" &&
    name.length == namePrefix.length + 64 + 5 &&
    label.all (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))

private def statusFileParent (path : String) : String :=
  String.intercalate "/" (path.splitOn "/" |>.dropLast)

private def pinnedPaymaster : ChainId → String
  | .mainnet => "0xB0FfCdC890E969579D348F519a9C3920C2DD04a5"
  | .sepolia => "0x835ce2da8ad0d1f5d5a8462a58594006514c39b0"

private def parseEvent (chainId : ChainId) (json : Json) :
    Except String Events.ExpectedWithdrawal := do
  let pool ← address (← string json "poolAddress")
  let known := (poolsFor chainId).any fun item =>
    item.address.toLower == (addressText pool).toLower
  if !known then throw invalid
  let nullifierHash ← hex (← string json "nullifierHash") 32
  let recipient ← address (← string json "recipient")
  let relayer ← address (← string json "relayer") true
  let fee ← JsonRpc.parseHexQuantity (← string json "fee")
  return ⟨pool, recipient, nullifierHash, relayer, fee⟩

structure Candidate where
  userOpHash : ByteArray
  events : List Events.ExpectedWithdrawal
  transactionHash : Option ByteArray
  deriving Inhabited

structure Record where
  chainId : ChainId
  rpcUrl : String
  bundlerUrl : String
  selectedUserOpHash : ByteArray
  entryPoint : Nat
  sender : Nat
  paymaster : Nat
  nonce : Nat
  fromBlock : Nat
  events : List Events.ExpectedWithdrawal
  candidates : Array Candidate
  statusFiles : Array String
  deriving Inhabited

private def sameNoteIdentities (left right : List Events.ExpectedWithdrawal) : Bool :=
  left.map (fun event => (event.pool, event.nullifierHash)) ==
    right.map (fun event => (event.pool, event.nullifierHash))

private def sameEvents (left right : List Events.ExpectedWithdrawal) : Bool :=
  left.length == right.length && (left.zip right).all (fun (a, b) =>
    a.pool == b.pool && a.nullifierHash == b.nullifierHash &&
    a.recipient == b.recipient && a.relayer == b.relayer && a.fee == b.fee)

private def parseCandidate (chainId : ChainId) (rootEvents : List Events.ExpectedWithdrawal)
    (json : Json) : Except String Candidate := do
  let userOpHash ← hex (← string json "userOpHash") 32
  let rawEvents ← (← field json "events").getArr?
  if rawEvents.size != rootEvents.length then throw invalid
  let events ← rawEvents.toList.mapM (parseEvent chainId)
  if !sameNoteIdentities rootEvents events then throw invalid
  let status ← string json "status"
  if !["unknown", "pending", "confirmed", "failed"].contains status then throw invalid
  let transactionHash ← match ← optionalString json "transactionHash" with
    | none => pure none
    | some raw => (hex raw 32).map some
  return ⟨userOpHash, events, transactionHash⟩

/-- Strict public record parser. It validates each candidate's note identities
    before any RPC call, but cannot authenticate the duplicated status files. -/
def parseRecord (root : Json) : Except String Record := do
  let version ← (← field root "version").getNat?
  if version != 1 || (← string root "kind") != "batch-4337" then throw invalid
  let chainNumber ← (← field root "chainId").getNat?
  let some chainId := chainFromNat chainNumber | throw invalid
  let rpcUrl ← string root "rpcUrl"
  let bundlerUrl ← string root "bundlerUrl"
  if !HttpTransport.validRpcUrl rpcUrl || !HttpTransport.validRpcUrl bundlerUrl then
    throw "Batch status requires HTTPS or explicit loopback HTTP endpoints."
  let selectedUserOpHash ← hex (← string root "userOpHash") 32
  let entryPoint ← address (← string root "entryPointAddress")
  if entryPoint != (← address Tornado.Cli.SmartAccountShow.entryPoint) then throw invalid
  let sender ← address (← string root "sender")
  let paymaster ← address (← string root "paymaster")
  if paymaster != (← address (pinnedPaymaster chainId)) then throw invalid
  let nonce ← JsonRpc.parseHexQuantity (← string root "nonce")
  let fromBlock ← JsonRpc.parseHexQuantity (← string root "fromBlock")
  let rawEvents ← (← field root "events").getArr?
  if rawEvents.isEmpty || rawEvents.size > 12 then throw invalid
  let events ← rawEvents.toList.mapM (parseEvent chainId)
  let identities := events.map (·.nullifierHash)
  if identities.eraseDups.length != identities.length then throw invalid
  let rawCandidates ← (← field root "candidates").getArr?
  if rawCandidates.isEmpty || rawCandidates.size > 16 then throw invalid
  let candidates ← rawCandidates.mapM (parseCandidate chainId events)
  let hashes := candidates.toList.map (·.userOpHash)
  if hashes.eraseDups.length != hashes.length ||
      !(hashes.any (· == selectedUserOpHash)) then throw invalid
  let paths ← (← field root "statusFiles").getArr?
  if paths.size != events.length then throw invalid
  let statusFiles ← paths.mapM Json.getStr?
  if statusFiles.any (fun path => path.length > 4096 || !statusFileShape chainId path) ||
      statusFiles.any (fun path => statusFileParent path !=
        statusFileParent statusFiles[0]!) ||
      statusFiles.toList.eraseDups.length != statusFiles.size then throw invalid
  let status ← string root "status"
  if !["unknown", "pending", "confirmed", "failed", "rejected"].contains status then
    throw invalid
  let some selected := candidates.find? (·.userOpHash == selectedUserOpHash) | throw invalid
  if !sameEvents selected.events events then throw invalid
  return ⟨chainId, rpcUrl, bundlerUrl, selectedUserOpHash,
    entryPoint, sender, paymaster, nonce, fromBlock, events,
    candidates, statusFiles⟩

inductive CandidateStatus where
  | confirmed | failed | unknown
  deriving BEq, Inhabited

def CandidateStatus.text : CandidateStatus → String
  | .confirmed => "confirmed"
  | .failed => "failed"
  | .unknown => "unknown"

structure CandidateObservation where
  hash : ByteArray
  status : CandidateStatus
  transactionHash : Option ByteArray := none
  deriving Inhabited

private def entry (record : Record) (candidate : Candidate) : Events.ExpectedEntry :=
  ⟨record.entryPoint, candidate.userOpHash, record.sender,
    record.paymaster, record.nonce⟩

private def receiptOutcome (record : Record) (candidate : Candidate)
    (hash : ByteArray) (receipt : RpcReceipt.Receipt) : CandidateStatus :=
  match RpcReceipt.batchWithdrawalOutcome receipt hash (entry record candidate)
      candidate.events none with
  | .confirmed => .confirmed
  | .failed => .failed
  | .unknown => .unknown

private def findTransaction (record : Record) (candidate : Candidate)
    (fetch : JsonRpc.Method → Array Json → IO Json) : IO (Option ByteArray) := do
  try
    let filter := Json.mkObj [
      ("address", toJson (addressText record.entryPoint)),
      ("fromBlock", toJson (quantityText record.fromBlock)),
      ("toBlock", toJson ("latest" : String)),
      ("topics", toJson #[hashText Events.userOperationTopic,
        hashText candidate.userOpHash])]
    let result ← fetch .getLogs #[filter]
    let logs ← fromExcept result.getArr?
    if logs.size != 1 then return none
    let log := logs[0]!
    if (← fromExcept <| address (← fromExcept <| string log "address")) !=
        record.entryPoint then return none
    let topics ← fromExcept <| (← fromExcept (field log "topics")).getArr?
    if topics.size < 2 || topics[0]! != toJson (hashText Events.userOperationTopic) ||
        topics[1]! != toJson (hashText candidate.userOpHash) then return none
    if let .ok (.bool true) := field log "removed" then return none
    let block ← fromExcept <| JsonRpc.parseHexQuantity
      (← fromExcept <| string log "blockNumber")
    if block < record.fromBlock then return none
    return some (← fromExcept <| hex (← fromExcept <| string log "transactionHash") 32)
  catch _ => return none

private def candidateWith (record : Record) (candidate : Candidate)
    (fetchChain fetchBundler : JsonRpc.Method → Array Json → IO Json) :
    IO CandidateObservation := do
  let mut hash := candidate.transactionHash
  if hash.isNone then
    try
      let result ← fetchBundler .getUserOperationReceipt
        #[toJson (hashText candidate.userOpHash)]
      if result != .null then
        if let .ok (.str returned) := field result "userOpHash" then
          if (hex returned 32).toOption != some candidate.userOpHash then
            throw <| IO.userError "Bundler returned another UserOperation."
        let nested ← fromExcept (field result "receipt")
        if let .ok (.str rawHash) := field nested "transactionHash" then
          hash := (hex rawHash 32).toOption
    catch _ => pure ()
  if hash.isNone then hash ← findTransaction record candidate fetchChain
  let some txHash := hash
    | return ⟨candidate.userOpHash, .unknown, none⟩
  try
    let result ← fetchChain .getTransactionReceipt #[toJson (hashText txHash)]
    if result == .null then return ⟨candidate.userOpHash, .unknown, some txHash⟩
    let receipt ← fromExcept (RpcReceipt.parseReceipt result txHash)
    if receipt.blockNumber < record.fromBlock then
      return ⟨candidate.userOpHash, .unknown, some txHash⟩
    return ⟨candidate.userOpHash, receiptOutcome record candidate txHash receipt, some txHash⟩
  catch _ => return ⟨candidate.userOpHash, .unknown, some txHash⟩

structure Observation where
  status : CandidateStatus
  candidates : Array CandidateObservation
  transactionHash : Option ByteArray
  message : String
  deriving Inhabited

/-- Read-only batch evidence. A single included failed candidate cannot make
    the batch failed while another signed candidate remains uncertain. -/
def reconcileWith (raw : String)
    (fetchChain fetchBundler : JsonRpc.Method → Array Json → IO Json) :
    IO Observation := do
  if raw.toUTF8.size > 1024 * 1024 then throw <| IO.userError invalid
  let root ← fromExcept (Json.parse raw)
  let record ← fromExcept (parseRecord root)
  let actualChain ← fromExcept <| JsonRpc.parseHexQuantity
    (← fromExcept (← fetchChain .chainId #[]).getStr?)
  if actualChain != chainNumber record.chainId then
    throw <| IO.userError "The RPC endpoint is on a different network."
  let mut results := #[]
  for candidate in record.candidates do
    results := results.push (← candidateWith record candidate fetchChain fetchBundler)
  let confirmed := results.filter (·.status == .confirmed)
  let failed := results.filter (·.status == .failed)
  let status := if confirmed.size == 1 && failed.isEmpty then .confirmed
    else if confirmed.isEmpty && failed.size == results.size then .failed
    else .unknown
  let selectedHash := if status == .confirmed then confirmed[0]!.transactionHash
    else results.findSome? (·.transactionHash)
  let message := if status == .confirmed then ""
    else if status == .failed then
      "Execution failed, but the sponsoring note may be spent. Recover the smart account and check every selected note before retrying."
    else "Check every signed UserOperation and selected note before retrying; all note reservations remain in place."
  return ⟨status, results, selectedHash, message⟩

private def eraseField (json : Json) (name : String) : Json :=
  match json with
  | .obj values => .obj (values.erase name)
  | other => other

private def eraseOutcome (json : Json) : Json :=
  ["status", "transactionHash", "message"].foldl eraseField json

/-- Exposure phases can differ after an interrupted sequential mirror update.
They are progress hints, never permission to release or replace a candidate. -/
private def nativePhase (json : Json) : Except String (Option String) := do
  let phase ← optionalString json "phase"
  if phase.any (fun value => !["reserved", "exposed", "submitted", "unknown"].contains value) then
    throw "Invalid native batch exposure phase."
  return phase

private def phaseRank (phase : String) : Nat :=
  if phase == "unknown" then 3 else if phase == "submitted" then 2
  else if phase == "exposed" then 1 else 0

/-- Only observation fields, native exposure progress and the selected
aggregate candidate may differ. Signed payload bytes/hash, exact event tuples,
unknown reservation fields, note ordering and paths must remain identical. -/
private def reservation (json : Json) : Except String Json := do
  let _ ← parseRecord json
  let _ ← nativePhase json
  let candidates ← (← field json "candidates").getArr?
  let base := ["userOpHash", "events", "nativeBatchStatusSync", "phase"].foldl eraseField
    (eraseOutcome json)
  return base.setObjVal! "candidates" (Json.arr (candidates.map eraseOutcome))

structure Store where
  read : String → IO ByteArray
  replace : String → ByteArray → ByteArray → IO Unit

def protectedStore : Store := ⟨ProtectedIO.readPrivate, ProtectedIO.replacePrivate⟩

private structure Mirror where
  path : String
  bytes : ByteArray
  json : Json
  deriving Inhabited

private def decodeBytes (bytes : ByteArray) : Except String Json := do
  if bytes.size > 1024 * 1024 then throw invalid
  let some raw := String.fromUTF8? bytes | throw invalid
  let json ← Json.parse raw
  let _ ← parseRecord json
  return json

private def loadMirrors (store : Store) (selectedPath : String)
    (expected : Option ByteArray) : IO (Array Mirror) := do
  let initialBytes ← store.read selectedPath
  if expected.any (· != initialBytes) then
    throw <| IO.userError "The selected batch journal changed; inspect every mirror and rerun status."
  let initial ← fromExcept (decodeBytes initialBytes)
  let record ← fromExcept (parseRecord initial)
  if !record.statusFiles.contains selectedPath then
    throw <| IO.userError "Selected file is absent from its batch status file list."
  let identity ← fromExcept (reservation initial)
  let mut mirrors := #[]
  for path in record.statusFiles do
    let bytes ← store.read path
    let json ← fromExcept (decodeBytes bytes)
    if (← fromExcept (reservation json)) != identity then
      throw <| IO.userError "Batch journals have different signed candidates or note reservations; no journal was updated."
    mirrors := mirrors.push ⟨path, bytes, json⟩
  return mirrors

/-- Merge existing transaction hints without dropping or replacing one.
    Conflicting hints require manual inspection before any file is updated. -/
private def mergedBaseline (mirrors : Array Mirror) : Except String Json := do
  if mirrors.isEmpty then throw invalid
  let reference := mirrors[0]!.json
  let mut candidates ← (← field reference "candidates").getArr?
  let mut exposure : Option String := none
  for mirror in mirrors do
    if let some phase ← nativePhase mirror.json then
      if exposure.isNone || phaseRank phase > phaseRank (exposure.getD "reserved") then
        exposure := some phase
    let parsed ← parseRecord mirror.json
    for i in [0:candidates.size] do
      let prior ← optionalString candidates[i]! "transactionHash"
      let next := parsed.candidates[i]!.transactionHash
      if let some value := next then
        let valueText := hashText value
        if let some old := prior then
          if (← hex old 32) != value then throw "Batch candidate transaction hints conflict; no journal was updated."
        else candidates := candidates.set! i (candidates[i]!.setObjVal! "transactionHash" (toJson valueText))
  for mirror in mirrors do
    if let some hash ← optionalString mirror.json "transactionHash" then
      let hash ← hex hash 32
      if !(candidates.any (fun candidate =>
          ((optionalString candidate "transactionHash").toOption.bind
            (fun optional => optional.bind (fun raw => (hex raw 32).toOption))) == some hash)) then
        throw "A batch aggregate transaction hint is not retained by any signed candidate; no journal was updated."
  let result := reference.setObjVal! "candidates" (Json.arr candidates)
  return match exposure with
    | none => result
    | some phase => result.setObjVal! "phase" (toJson phase)

private def observedJson (baseline : Json) (observation : Observation) : Except String Json := do
  let record ← parseRecord baseline
  let candidates ← (← field baseline "candidates").getArr?
  if observation.candidates.size != candidates.size then throw invalid
  let mut updated := #[]
  for i in [0:candidates.size] do
    let observed := observation.candidates[i]!
    if observed.hash != record.candidates[i]!.userOpHash then throw invalid
    let prior := record.candidates[i]!.transactionHash
    if prior.isSome && observed.transactionHash != prior then throw invalid
    if observed.transactionHash.any (fun value => value.size != 32) then throw invalid
    let value := candidates[i]!.setObjVal! "status" (toJson observed.status.text)
    let value := match observed.transactionHash with
      | none => value
      | some hash => value.setObjVal! "transactionHash" (toJson (hashText hash))
    updated := updated.push value
  let chosen := if observation.status == .confirmed then
      observation.candidates.findIdx? (·.status == .confirmed)
    else none
  let selected := chosen.getD ((record.candidates.findIdx?
    (·.userOpHash == record.selectedUserOpHash)).getD 0)
  let root := eraseField baseline "nativeBatchStatusSync"
  let root := root.setObjVal! "candidates" (Json.arr updated)
  let root := root.setObjVal! "userOpHash" (← field updated[selected]! "userOpHash")
  let root := root.setObjVal! "events" (← field updated[selected]! "events")
  let root := root.setObjVal! "status" (toJson observation.status.text)
  let root := root.setObjVal! "message" (toJson observation.message)
  let root := match observation.transactionHash with
    | none => root
    | some hash => root.setObjVal! "transactionHash" (toJson (hashText hash))
  let _ ← parseRecord root
  if (← reservation root) != (← reservation baseline) then throw invalid
  return root

private def syncMarker (root : Json) (phase : String) : Json :=
  root.setObjVal! "nativeBatchStatusSync" (Json.mkObj [
    ("version", toJson (1 : Nat)), ("state", toJson phase),
    ("authoritativeFile", (root.getObjVal? "statusFiles" >>= Json.getArr?).toOption
      |>.bind (·[0]?) |>.getD Json.null),
    ("releaseReservations", toJson false)])

structure PersistenceResult where
  observation : Observation
  complete : Bool
  acknowledgedMirrors : Nat
  totalMirrors : Nat
  message : String
  deriving Inhabited

/-- Pre-read every mirror and reconcile one union of known transaction hints.
    The first record is authoritative for this update's completion marker.
    A partial or ambiguous CAS never deletes a reservation or candidate, and
    produces an explicit incomplete result instead of a safe-retry signal. -/
def reconcileAndPersistWith (selectedPath : String) (store : Store)
    (fetchChain fetchBundler : JsonRpc.Method → Array Json → IO Json)
    (expected : Option ByteArray := none) : IO PersistenceResult := do
  let mirrors ← loadMirrors store selectedPath expected
  let baseline ← fromExcept (mergedBaseline mirrors)
  let observation ← reconcileWith baseline.compress fetchChain fetchBundler
  let updated ← fromExcept (observedJson baseline observation)
  let staged := ((syncMarker updated "in-progress").compress ++ "\n").toUTF8
  let complete := ((syncMarker updated "complete").compress ++ "\n").toUTF8
  if staged.size > 1024 * 1024 || complete.size > 1024 * 1024 then
    throw <| IO.userError invalid
  let mut acknowledged := 0
  for mirror in mirrors do
    try
      store.replace mirror.path mirror.bytes staged
      acknowledged := acknowledged + 1
    catch _ =>
      return ⟨observation, false, acknowledged, mirrors.size,
        s!"Batch journal synchronization is incomplete ({acknowledged}/{mirrors.size} mirror writes acknowledged). A write may have completed before its error. Keep every reservation and signed hash; inspect all listed files and rerun status. Do not prepare a replacement withdrawal."⟩
  try
    store.replace mirrors[0]!.path staged complete
    return ⟨observation, true, acknowledged, mirrors.size,
      "Batch observation saved to every journal. All signed candidates and note reservations remain in place."⟩
  catch _ =>
    return ⟨observation, false, acknowledged, mirrors.size,
      "All mirror writes were acknowledged, but the authoritative completion marker could not be committed. Keep every reservation and signed hash, inspect all listed files and rerun status before further action."⟩

def render (observation : Observation) : String :=
  let lines := observation.candidates.toList.zipIdx.map fun (candidate, index) =>
    s!"Candidate {index + 1}: {candidate.status.text}\t{hashText candidate.hash}" ++
      (candidate.transactionHash.map (fun hash => "\t" ++ hashText hash) |>.getD "")
  "Status: " ++ observation.status.text ++ "\n" ++
  String.intercalate "\n" lines ++ "\n" ++
  (observation.transactionHash.map (fun hash =>
    "Transaction: " ++ hashText hash ++ "\n") |>.getD "") ++
  (if observation.message.isEmpty then "" else observation.message ++ "\n")

private structure Options where
  statusFile : Option String := none
  rpc : Option String := none
  bundlerUrl : Option String := none
  help : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with help := true }
  | "--status-file" :: value :: rest => parseOptions rest { options with statusFile := some value }
  | "--rpc" :: value :: rest => parseOptions rest { options with rpc := some value }
  | "--bundler-url" :: value :: rest => parseOptions rest { options with bundlerUrl := some value }
  | ["--status-file"] => .error "error: option '--status-file <path>' argument missing"
  | ["--rpc"] => .error "error: option '--rpc <url>' argument missing"
  | ["--bundler-url"] => .error "error: option '--bundler-url <url>' argument missing"
  | item :: rest =>
      if item.startsWith "--status-file=" then
        parseOptions rest { options with statusFile := some (String.ofList (item.toList.drop 14)) }
      else if item.startsWith "--rpc=" then
        parseOptions rest { options with rpc := some (String.ofList (item.toList.drop 6)) }
      else if item.startsWith "--bundler-url=" then
        parseOptions rest { options with bundlerUrl := some (String.ofList (item.toList.drop 14)) }
      else .error s!"error: unknown option '{item}'"

private def help : String :=
  "Usage: tornado withdraw status --status-file <path> [--rpc <url>] [--bundler-url <url>]\n\n" ++
  "Reconcile all signed batch-4337 candidates and update every protected note journal.\n"

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
    | throw <| IO.userError "Private batch status file is not UTF-8."
  let record ← fromExcept (parseRecord (← fromExcept (Json.parse raw)))
  if !record.statusFiles.contains absolute then
    throw <| IO.userError "Selected file is absent from its batch status file list."
  let rpc := options.rpc.getD record.rpcUrl
  let bundler := options.bundlerUrl.getD record.bundlerUrl
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
  let result ← reconcileAndPersistWith absolute protectedStore fetchChain fetchBundler (some bytes)
  return (render result.observation ++ result.message ++ "\n",
    if result.complete && result.observation.status == .confirmed then 0 else 2)

end Tornado.Cli.BatchWithdrawalStatus
