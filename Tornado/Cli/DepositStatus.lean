import Lean
import Tornado.Domain.Catalog
import Tornado.Domain.NoteIdentity
import Tornado.Protocol.RpcReceipt
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.ProtectedIO

/-!
Read-only inspection of a sequential deposit journal. This module returns
observations without persisting them; command-level journal reconciliation
is handled separately by `DepositStatusCommand`.
-/

namespace Tornado.Cli.DepositStatus

open Lean Tornado.Domain Tornado.Protocol Tornado.Runtime

inductive StepKind where
  | reset | approve | deposit
  deriving Repr, BEq, DecidableEq, Inhabited

inductive StepStatus where
  | planned | prepared | submitted | confirmed | reverted | unknown
  deriving Repr, BEq, DecidableEq, Inhabited

def StepStatus.text : StepStatus → String
  | .planned => "planned"
  | .prepared => "prepared"
  | .submitted => "submitted"
  | .confirmed => "confirmed"
  | .reverted => "reverted"
  | .unknown => "unknown"

private def parseStatus : String → Except String StepStatus
  | "planned" => .ok .planned
  | "prepared" => .ok .prepared
  | "submitted" => .ok .submitted
  | "confirmed" => .ok .confirmed
  | "reverted" => .ok .reverted
  | "unknown" => .ok .unknown
  | _ => .error "Unsupported sequential deposit step status."

private def parseKind : String → Except String StepKind
  | "reset" => .ok .reset
  | "approve" => .ok .approve
  | "deposit" => .ok .deposit
  | _ => .error "Unsupported sequential deposit step kind."

structure Step where
  kind : StepKind
  label : String
  to : Nat
  status : StepStatus
  hash : Option String := none
  expectedDeposit : Option Events.ExpectedDeposit := none
  deriving Inhabited

structure Journal where
  chainId : ChainId
  account : Nat
  steps : Array Step
  deriving Inhabited

private def invalid : String := "This is not a supported sequential deposit journal."

private def fieldString (json : Json) (name : String) : Except String String := do
  (← json.getObjVal? name).getStr?

private def optionalString (json : Json) (name : String) : Except String (Option String) :=
  match json.getObjVal? name with
  | .error _ => .ok none
  | .ok value => (value.getStr?).map some

private def exactHex (raw : String) (width : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw invalid
  let bytes ← parseHexBytes raw
  if bytes.size != width then throw invalid
  return bytes

private def address (raw : String) : Except String Nat := do
  let bytes ← exactHex raw 20
  let value := bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  if value == 0 then throw invalid
  return value

private def safeLabel (value : String) : Bool :=
  !value.isEmpty && value.length <= 256 &&
    value.toList.all (fun char => char.toNat >= 32 && char.toNat <= 126)

private def parseStep (chainId : ChainId) (json : Json) : Except String Step := do
  let kind ← parseKind (← fieldString json "kind")
  let label ← fieldString json "label"
  if !safeLabel label then throw invalid
  let to ← address (← fieldString json "to")
  let status ← parseStatus (← fieldString json "status")
  let hash ← optionalString json "hash"
  if hash.isSome then
    let _ ← exactHex hash.get! 32
    pure ()
  else if status != .planned then throw invalid
  let mut expectedDeposit := none
  if kind == .deposit then
    let poolAddress ← address (← fieldString json "pool")
    let commitment ← exactHex (← fieldString json "commitment") 32
    let denomination ← fieldString json "denomination"
    let asset ← fieldString json "asset"
    let some pool := poolFor chainId denomination asset | throw invalid
    let catalogAddress ← address pool.address
    if poolAddress != catalogAddress || to != catalogAddress then throw invalid
    expectedDeposit := some ⟨poolAddress, commitment⟩
  return { kind, label, to, status, hash, expectedDeposit }

/-- Reject malformed or mixed-network journals before querying any RPC.
    The generated TypeScript journal has at most 100 deposits plus approvals;
    this 300-step bound is a conservative parser/resource limit. -/
def parseJournal (raw : String) : Except String Journal := do
  let json ← Json.parse raw
  let version ← (← json.getObjVal? "version").getNat?
  if version != 1 || (← fieldString json "kind") != "deposit" then throw invalid
  let chainNumber ← (← json.getObjVal? "chainId").getNat?
  let some chainId := chainFromNat chainNumber | throw invalid
  let account ← address (← fieldString json "account")
  let _ ← fieldString json "createdAt"
  let rawSteps ← (← json.getObjVal? "steps").getArr?
  if rawSteps.isEmpty || rawSteps.size > 300 then throw invalid
  let mut steps := #[]
  let mut hashes : List String := []
  for item in rawSteps do
    let step ← parseStep chainId item
    if let some hash := step.hash then
      if hashes.contains hash.toLower then throw invalid
      hashes := hash.toLower :: hashes
    steps := steps.push step
  return ⟨chainId, account, steps⟩

/-- Classify one chain receipt. Missing or mismatched evidence is unknown.
    A reverted receipt is definitive only when its hash,
    sender, and destination match the journal step. -/
def classify (journal : Journal) (step : Step)
    (receipt : Option RpcReceipt.Receipt) : StepStatus :=
  match step.hash with
  | none => step.status
  | some hash =>
    match receipt with
    | none => .unknown
    | some value =>
      if (exactHex hash 32).toOption != some value.transactionHash ||
          value.origin != journal.account || value.to != some step.to then .unknown
      else if !value.success then .reverted
      else match step.kind, step.expectedDeposit with
        | .deposit, some expected =>
          if Events.hasDeposit value.logs expected then .confirmed else .unknown
        | .deposit, none => .unknown
        | _, _ => .confirmed

def render (journal : Journal) (states : Array StepStatus) : Except String String := do
  if states.size != journal.steps.size then throw "Status count differs from journal steps."
  let lines := (journal.steps.zip states).toList.zipIdx.map fun ((step, status), index) =>
    s!"{index + 1}. {status.text}\t{step.label}{step.hash.map ("\t" ++ ·) |>.getD ""}"
  return String.intercalate "\n" lines ++ "\nRead-only inspection; journal statuses were not updated.\n"

private structure Options where
  journal : Option String := none
  rpc : Option String := none
  showHelp : Bool := false
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Except String Options :=
  match args with
  | [] => .ok options
  | "-h" :: _ | "--help" :: _ => .ok { options with showHelp := true }
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

private def help : String :=
  "Usage: tornado deposit inspect-status --journal <path> [--rpc <url>]\n\n" ++
  "Inspect a sequential deposit journal against chain receipts without updating it.\n" ++
  "Batched 7702 journals are not supported yet.\n"

private def fromExcept (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

/-- Read-only network command, suitable only for a separately named CLI
    surface. The RPC remains an external chain-truth assumption. -/
def inspectCommand (args : List String) : IO String := do
  let options ← fromExcept (parseOptions args)
  if options.showHelp then return help
  let some file := options.journal
    | throw <| IO.userError "error: required option '--journal <path>' not specified"
  let current ← IO.currentDir
  let absolute := if (System.FilePath.mk file).isAbsolute then file
    else (current / file).toString
  let bytes ← ProtectedIO.readPrivate absolute
  let some raw := String.fromUTF8? bytes
    | throw <| IO.userError "Private deposit journal is not UTF-8."
  let journal ← fromExcept (parseJournal raw)
  let environmentRpc ← IO.getEnv "TORNADO_RPC_URL"
  let rpc := (options.rpc.orElse (fun _ => environmentRpc)).getD
    (defaultRpc journal.chainId)
  let id ← HttpTransport.call rpc 1 .chainId #[]
  let network ← fromExcept (JsonRpc.parseHexQuantity (← fromExcept id.getStr?))
  if network != chainNumber journal.chainId then
    throw <| IO.userError "The RPC endpoint is on a different network."
  let mut states := #[]
  for index in [0:journal.steps.size] do
    let step := journal.steps[index]!
    let mut receipt : Option RpcReceipt.Receipt := none
    if let some hash := step.hash then
      let expectedHash ← fromExcept (exactHex hash 32)
      try
        let result ← HttpTransport.call rpc (index + 2) .getTransactionReceipt
          #[toJson hash]
        if result != .null then
          receipt := (RpcReceipt.parseReceipt result expectedHash).toOption
      catch _ => pure ()
    states := states.push (classify journal step receipt)
  fromExcept (render journal states)

end Tornado.Cli.DepositStatus
