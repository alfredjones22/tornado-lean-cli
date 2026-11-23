import Lean
import Tornado.Domain.Catalog
import Tornado.Domain.NoteIdentity
import Tornado.Crypto.Keccak
import Tornado.Protocol.RpcReceipt
import Tornado.Protocol.Abi
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.ProtectedIO

/-!
Reconciliation of the pinned smart-account recovery journal. A fresh chain
observation replaces the protected record by exact byte compare-and-replace.
The recorded transaction hash and calldata hash are checked before a receipt
can be called confirmed. RPC truth/finality remain external.
-/

namespace Tornado.Cli.SmartAccountStatus

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime

inductive Status where
  | prepared | submitted | confirmed | failed | unknown
  deriving Repr, BEq, DecidableEq, Inhabited

def Status.text : Status → String
  | .prepared => "prepared"
  | .submitted => "submitted"
  | .confirmed => "confirmed"
  | .failed => "failed"
  | .unknown => "unknown"

private def parseStatus : String → Except String Status
  | "prepared" => .ok .prepared
  | "submitted" => .ok .submitted
  | "confirmed" => .ok .confirmed
  | "failed" => .ok .failed
  | "unknown" => .ok .unknown
  | _ => .error "Invalid smart-account recovery journal status."

structure Journal where
  chainId : ChainId
  owner : Nat
  account : Nat
  recipient : Nat
  transactionHash : ByteArray
  calldataHash : ByteArray
  priorStatus : Status
  deriving Inhabited

structure Observation where
  status : Status
  message : Option String := none
  deriving Inhabited

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def string (json : Json) (name : String) : Except String String := do
  (← field json name).getStr?

private def fixedHex (raw : String) (width : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw "Invalid recovery journal or RPC hex value."
  let bytes ← parseHexBytes raw
  if bytes.size != width then throw "Invalid recovery journal or RPC hex width."
  return bytes

private def address (raw : String) : Except String Nat := do
  let bytes ← fixedHex raw 20
  let value := bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  if value == 0 then throw "Zero address in recovery journal or RPC transaction."
  return value

/-- Parse the protected TypeScript recovery record before any network call.
    This is intentionally stricter than the source's permissive JSON cast. -/
def parseJournal (raw : String) : Except String Journal := do
  if raw.toUTF8.size > 1024 * 1024 then
    throw "Smart-account recovery journal exceeds one MiB."
  let json ← Json.parse raw
  if (← (← field json "version").getNat?) != 1 ||
      (← string json "kind") != "smart-account-recovery" then
    throw "Invalid smart-account recovery journal."
  let chainNumber ← (← field json "chainId").getNat?
  let some chainId := chainFromNat chainNumber
    | throw "Unsupported recovery journal chain."
  let owner ← address (← string json "owner")
  let account ← address (← string json "account")
  let recipient ← address (← string json "recipient")
  if owner == account || recipient == account then
    throw "Recovery journal owner, account, and recipient are inconsistent."
  let transactionHash ← fixedHex (← string json "transactionHash") 32
  let calldataHash ← fixedHex (← string json "calldataHash") 32
  let priorStatus ← parseStatus (← string json "status")
  return { chainId, owner, account, recipient, transactionHash,
           calldataHash, priorStatus }

private def addressText (value : Nat) : Except String String := do
  if value == 0 || value >= 2 ^ 160 then throw "Invalid recovery journal address."
  let bytes ← Tornado.Protocol.Abi.addressWord value
  return "0x" ++ bytesToHex (bytes.extract 12 32)

/-- The TypeScript-compatible recovery record contains public transaction
    identity only. The caller must create or CAS-replace it through protected
    file IO before exposing a signed transaction. -/
def journalBytes (journal : Journal) (status : Status)
    (message : Option String := none) : Except String ByteArray := do
  if journal.transactionHash.size != 32 || journal.calldataHash.size != 32 ||
      journal.owner == journal.account || journal.recipient == journal.account then
    throw "Invalid recovery journal transaction identity."
  let mut fields := [
    ("version", toJson (1 : Nat)),
    ("kind", toJson ("smart-account-recovery" : String)),
    ("chainId", toJson (chainNumber journal.chainId)),
    ("owner", toJson (← addressText journal.owner)),
    ("account", toJson (← addressText journal.account)),
    ("recipient", toJson (← addressText journal.recipient)),
    ("transactionHash", toJson ("0x" ++ bytesToHex journal.transactionHash)),
    ("calldataHash", toJson ("0x" ++ bytesToHex journal.calldataHash)),
    ("status", toJson status.text)]
  if let some text := message then
    if text.toUTF8.size > 1024 then throw "Recovery journal message is too large."
    fields := fields ++ [("message", toJson text)]
  return ((Json.mkObj fields).compress ++ "\n").toUTF8

private def data (raw : String) : Except String ByteArray := do
  if !raw.startsWith "0x" || raw.length > 2 * 1024 * 1024 + 2 then
    throw "Recovery transaction input is missing or too large."
  parseHexBytes raw

/-- Bind an indexed transaction to the recorded signed hash, sender,
    destination, calldata hash, and (when present) chain ID. -/
def transactionMatches (journal : Journal) (transaction : Json) : Except String Bool := do
  if transaction == .null then return false
  let hash ← fixedHex (← string transaction "hash") 32
  let owner ← address (← string transaction "from")
  let account ← address (← string transaction "to")
  let input ← data (← string transaction "input")
  let value ← JsonRpc.parseHexQuantity (← string transaction "value")
  let kind ← JsonRpc.parseHexQuantity (← string transaction "type")
  if value != 0 || kind != 2 then return false
  if let .ok chain := transaction.getObjVal? "chainId" then
    let number ← JsonRpc.parseHexQuantity (← chain.getStr?)
    if number != chainNumber journal.chainId then return false
  return hash == journal.transactionHash && owner == journal.owner &&
    account == journal.account && keccak256 input == journal.calldataHash

/-- A receipt is evidence for the indexed transaction only when both RPC
    responses refer to the same inclusion. Pending transaction metadata cannot
    be paired with an old receipt after a provider-side reorg race. -/
def transactionInclusionMatches (transaction : Json)
    (receipt : RpcReceipt.Receipt) : Except String Bool := do
  let blockHash ← fixedHex (← string transaction "blockHash") 32
  let blockNumber ← JsonRpc.parseHexQuantity (← string transaction "blockNumber")
  let transactionIndex ← JsonRpc.parseHexQuantity (← string transaction "transactionIndex")
  return blockHash == receipt.blockHash && blockNumber == receipt.blockNumber &&
    transactionIndex == receipt.transactionIndex

/-- A missing or mismatched transaction is uncertain. A receipt can confirm
    only the exact recorded transaction, sender, and account destination. -/
private def uncertain (message : String) : Observation :=
  { status := .unknown, message := some message }

def observe (journal : Journal) (transaction receipt : Json) : Observation :=
  if transaction == .null then
    uncertain "Recovery transaction is not indexed yet. Check the hash before retrying."
  else match transactionMatches journal transaction with
  | .error _ => uncertain "The indexed transaction is malformed or differs from the recorded recovery call."
  | .ok false => uncertain "The indexed transaction differs from the recorded recovery call."
  | .ok true =>
      if receipt == .null then
        { status := .submitted, message := some "Recovery transaction is pending." }
      else match RpcReceipt.parseReceipt receipt journal.transactionHash with
      | .error _ => uncertain "The recovery receipt is malformed or differs from the recorded transaction."
      | .ok parsed =>
          match transactionInclusionMatches transaction parsed with
          | .ok true =>
              if parsed.origin != journal.owner || parsed.to != some journal.account then
                uncertain "The recovery receipt differs from the recorded sender or account."
              else if parsed.success then { status := .confirmed }
              else { status := .failed }
          | _ => uncertain "The recovery transaction and receipt disagree on block inclusion."

theorem confirmed_requires_matching_transaction (journal : Journal)
    (transaction receipt : Json)
    (h : (observe journal transaction receipt).status = .confirmed) :
    transactionMatches journal transaction = .ok true := by
  unfold observe at h
  by_cases hn : transaction == Json.null
  · simp [hn, uncertain] at h
  · simp only [hn, Bool.false_eq_true, ↓reduceIte] at h
    cases hm : transactionMatches journal transaction with
    | error _ => simp [hm, uncertain] at h
    | ok matched =>
        cases matched with
        | false => simp [hm, uncertain] at h
        | true => rfl

theorem confirmed_requires_matching_inclusion (journal : Journal)
    (transaction receipt : Json)
    (h : (observe journal transaction receipt).status = .confirmed) :
    ∃ parsed, RpcReceipt.parseReceipt receipt journal.transactionHash = .ok parsed ∧
      transactionInclusionMatches transaction parsed = .ok true := by
  have hm := confirmed_requires_matching_transaction journal transaction receipt h
  have hn : (transaction == Json.null) = false := by
    cases heq : (transaction == Json.null) with
    | false => rfl
    | true => simp [observe, heq, uncertain] at h
  have hr : (receipt == Json.null) = false := by
    cases heq : (receipt == Json.null) with
    | false => rfl
    | true => simp [observe, hn, hm, heq] at h
  cases hp : RpcReceipt.parseReceipt receipt journal.transactionHash with
  | error message =>
      simp [observe, hn, hm, hr, hp, uncertain] at h
  | ok parsed =>
      cases hi : transactionInclusionMatches transaction parsed with
      | error message =>
          simp [observe, hn, hm, hr, hp, hi, uncertain] at h
      | ok matched =>
          cases matched with
          | false =>
              simp [observe, hn, hm, hr, hp, hi, uncertain] at h
          | true => exact ⟨parsed, rfl, hi⟩

def render (journal : Journal) (observation : Observation) : String :=
  "Status: " ++ observation.status.text ++ "\n" ++
  "Transaction: 0x" ++ bytesToHex journal.transactionHash ++ "\n" ++
  (observation.message.map (· ++ "\n")).getD ""

private structure Options where
  journal : Option String := none
  rpc : Option String := none
  help : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with help := true }
  | "--journal" :: value :: rest => parseOptions rest { options with journal := some value }
  | "--rpc" :: value :: rest => parseOptions rest { options with rpc := some value }
  | ["--journal"] => .error "error: option '--journal <path>' argument missing"
  | ["--rpc"] => .error "error: option '--rpc <url>' argument missing"
  | item :: rest =>
      if item.startsWith "--journal=" then
        parseOptions rest { options with journal := some (String.ofList (item.toList.drop 10)) }
      else if item.startsWith "--rpc=" then
        parseOptions rest { options with rpc := some (String.ofList (item.toList.drop 6)) }
      else .error s!"error: unknown option '{item}'"

private def commandHelp : String :=
  "Usage: tornado smart-account status --journal <path> [--rpc <url>]\n\n" ++
  "Check a recovery transaction against chain receipts and update its protected journal.\n"

private def fromExcept (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

/-- The fetch callback permits exact offline fault tests. The live adapter
    below sends only chain ID, transaction and receipt read requests. -/
def inspectWith (journal : Journal)
    (fetch : JsonRpc.Method → Array Json → IO Json) : IO Observation := do
  let chain ← fetch .chainId #[]
  let number ← fromExcept <| JsonRpc.parseHexQuantity (← fromExcept chain.getStr?)
  if number != chainNumber journal.chainId then
    throw <| IO.userError "The RPC endpoint is on a different network."
  let hash := "0x" ++ bytesToHex journal.transactionHash
  let transaction ← try fetch .getTransactionByHash #[toJson hash]
    catch _ => pure .null
  if transaction == .null then return observe journal .null .null
  let receipt ← try fetch .getTransactionReceipt #[toJson hash]
    catch _ => pure .null
  return observe journal transaction receipt

/-- Reconcile exactly the snapshot that was read, then atomically replace
    only that snapshot. A concurrent writer or failed durable write cannot
    silently discard another process's transaction status. -/
def reconcileWith (prior : ByteArray)
    (fetch : JsonRpc.Method → Array Json → IO Json)
    (replace : ByteArray → ByteArray → IO Unit) : IO (Journal × Observation) := do
  let some raw := String.fromUTF8? prior
    | throw <| IO.userError "Private recovery journal is not UTF-8."
  let journal ← fromExcept (parseJournal raw)
  let observation ← inspectWith journal fetch
  let next ← fromExcept <| journalBytes journal observation.status observation.message
  replace prior next
  return (journal, observation)

def statusCommand (args : List String) : IO (String × UInt32) := do
  let options ← fromExcept (parseOptions args)
  if options.help then return (commandHelp, 0)
  let some file := options.journal
    | throw <| IO.userError "error: required option '--journal <path>' not specified"
  let current ← IO.currentDir
  let absolute := if (System.FilePath.mk file).isAbsolute then file
    else (current / file).toString
  let bytes ← ProtectedIO.readPrivate absolute
  let some raw := String.fromUTF8? bytes
    | throw <| IO.userError "Private recovery journal is not UTF-8."
  let journal ← fromExcept (parseJournal raw)
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD
    (defaultRpc journal.chainId)
  let id ← IO.mkRef (1 : Nat)
  let fetch (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let next ← id.get
    id.set (next + 1)
    HttpTransport.call rpc next method params
  let (_, observation) ← reconcileWith bytes fetch (ProtectedIO.replacePrivate absolute)
  return (render journal observation,
    if observation.status == .confirmed then 0 else 2)

end Tornado.Cli.SmartAccountStatus

#print axioms Tornado.Cli.SmartAccountStatus.confirmed_requires_matching_transaction
#print axioms Tornado.Cli.SmartAccountStatus.confirmed_requires_matching_inclusion
