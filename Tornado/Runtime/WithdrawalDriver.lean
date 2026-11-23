import Tornado.Runtime.Bundler

/-! The finite command machine interpreted by the runnable sponsored withdrawal
runner. Callback success acknowledges the documented IO contract; kernel proofs
do not prove OS durability, signer behavior or chain truth. A callback may fail
after performing its effect: every such response is admitted conservatively.
-/

namespace Tornado.Runtime.WithdrawalDriver

open Lean Tornado.Crypto Tornado.Protocol Tornado.Protocol.UserOperation08

inductive Flow where
  | direct | batch
  deriving BEq, DecidableEq, Inhabited

structure NoteId where
  pool : Nat
  nullifierHash : Nat
  deriving BEq, DecidableEq, Inhabited

/-- The unsigned operation is an index, rather than a hash-only association. -/
structure ReviewedOperation (unsigned : UserOperation) where
  private mk ::
  chainId : Nat
  owner : Nat
  selected : Array NoteId
  flow : Flow
  preparedAtMs : Nat
  text : String
  bounds : Bundler.Bounds
  hash : ByteArray
  hashed : userOperationHash chainId Bundler.entryPoint unsigned = .ok hash

def prepareReviewed (chainId owner : Nat) (unsigned : UserOperation)
    (selected : Array NoteId) (flow : Flow) (preparedAtMs : Nat) (text : String)
    (bounds : Bundler.Bounds := {}) : Except String (ReviewedOperation unsigned) := do
  if (chainId != 1 && chainId != 11155111) || owner == 0 || owner >= 2 ^ 160 ||
      !unsigned.signature.isEmpty || selected.isEmpty || selected.size > 12 ||
      selected.toList.eraseDups.length != selected.size then
    throw "Invalid reviewed withdrawal operation."
  Bundler.validate unsigned bounds
  match hashed : userOperationHash chainId Bundler.entryPoint unsigned with
  | .error message => throw message
  | .ok hash => return ⟨chainId, owner, selected, flow, preparedAtMs, text, bounds, hash, hashed⟩

structure Signed where
  owner : Nat
  signature : ByteArray
  authorization : Option Bundler.Authorization := none

def canonicalSignature (signature : ByteArray) : Bool := Id.run do
  if signature.size != 65 then return false
  let word (start : Nat) := (signature.extract start (start + 32)).data.foldl
    (fun n byte => n * 256 + byte.toNat) 0
  let r := word 0
  let s := word 32
  return r > 0 && r < secp256k1Order && s > 0 && s <= secp256k1Order / 2 &&
    (signature[64]! == 27 || signature[64]! == 28)

def authorizationAllowed (flow : Flow) (chainId : Nat)
    (authorization : Option Bundler.Authorization) : Bool :=
  match flow, authorization with
  | .direct, some auth => auth.chainId == chainId && auth.nonce == 0 &&
      auth.delegate == 0xe6cae83bde06e4c305530e199d7217f42808555b
  | .batch, none => true
  | _, _ => false

/-- Complete executable payload, including the separate 7702 authorization.
Only the signature may differ from the indexed reviewed operation. -/
structure FinalPayload {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) where
  private mk ::
  signed : Signed
  operation : UserOperation
  json : Json
  bytes : ByteArray
  operationExact : operation = { unsigned with signature := signed.signature }
  ownerBound : signed.owner = reviewed.owner
  signatureCanonical : canonicalSignature signed.signature = true
  authorizationBound : authorizationAllowed reviewed.flow reviewed.chainId signed.authorization = true
  hashBound : userOperationHash reviewed.chainId Bundler.entryPoint operation = .ok reviewed.hash
  jsonBound : Bundler.withAuthorization reviewed.chainId operation signed.authorization = .ok json
  bytesBound : bytes = json.compress.toUTF8

def finalize {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned)
    (signed : Signed) : Except String (FinalPayload reviewed) := do
  if ownerBound : signed.owner = reviewed.owner then
    if signatureCanonical : canonicalSignature signed.signature = true then
      if authorizationBound : authorizationAllowed reviewed.flow reviewed.chainId signed.authorization = true then
        let operation := { unsigned with signature := signed.signature }
        Bundler.validate operation reviewed.bounds
        match hashed : userOperationHash reviewed.chainId Bundler.entryPoint operation with
        | .error message => throw message
        | .ok hash =>
          if equal : hash = reviewed.hash then
            match encoded : Bundler.withAuthorization reviewed.chainId operation signed.authorization with
            | .error message => throw message
            | .ok json =>
              if json.compress.utf8ByteSize > Bundler.maxOperationBytes then
                throw "Final withdrawal payload exceeds its transport bound."
              return ⟨signed, operation, json, json.compress.toUTF8, rfl, ownerBound,
                signatureCanonical, authorizationBound, hashed.trans (congrArg Except.ok equal), encoded, rfl⟩
          else throw "Final signed withdrawal differs from review."
      else throw "Withdrawal authorization differs from the reviewed policy."
    else throw "Owner signature is not canonical Ethereum ECDSA."
  else throw "Signing key differs from the reviewed withdrawal owner."

inductive Kind where
  | approve | afterApprovalClock | revalidate | beforeSignClock | sign | afterSignClock
  | reserve | markExposed | simulate | send | markSubmitted | markUnknown
  deriving BEq, DecidableEq, Repr, Inhabited

inductive Command {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) where
  | approve | afterApprovalClock | revalidate | beforeSignClock | sign | afterSignClock
  | reserve (payload : FinalPayload reviewed)
  | markExposed (payload : FinalPayload reviewed)
  | simulate (payload : FinalPayload reviewed)
  | send (payload : FinalPayload reviewed)
  | markSubmitted (payload : FinalPayload reviewed)
  | markUnknown (payload : FinalPayload reviewed)

def Command.kind {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned} : Command reviewed → Kind
  | .approve => .approve | .afterApprovalClock => .afterApprovalClock
  | .revalidate => .revalidate | .beforeSignClock => .beforeSignClock
  | .sign => .sign | .afterSignClock => .afterSignClock | .reserve _ => .reserve
  | .markExposed _ => .markExposed | .simulate _ => .simulate | .send _ => .send
  | .markSubmitted _ => .markSubmitted | .markUnknown _ => .markUnknown

structure Observation where
  kind : Kind
  accepted : Bool
  deriving BEq, DecidableEq, Repr

inductive Phase where
  | approve | afterApprovalClock | revalidate | beforeSignClock | sign | afterSignClock
  | reserve | markExposed | simulate | send | markSubmitted | markUnknown
  | submitted | unknown | blocked
  deriving BEq, DecidableEq, Repr, Inhabited

structure State {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) where
  private mk ::
  phase : Phase
  history : List Observation
  payload : Option (FinalPayload reviewed)

def initial {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) : State reviewed :=
  ⟨.approve, [], none⟩

def called {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (state : State reviewed) (kind : Kind) : Bool := state.history.any (·.kind == kind)

def acknowledged {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (state : State reviewed) (kind : Kind) : Bool :=
  state.history.any (fun event => event.kind == kind && event.accepted)

def locked {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (state : State reviewed) : Bool :=
  called state .markExposed || called state .simulate || called state .send || called state .markUnknown

def readyForExposure {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (state : State reviewed) : Bool :=
  acknowledged state .approve && acknowledged state .revalidate &&
    acknowledged state .sign && acknowledged state .reserve && acknowledged state .markExposed

/-- These are the exact instructions dispatched by `runFuel`; guards refer to
the completed callback trace, not caller-supplied durable flags or counters. -/
def next {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (state : State reviewed) : Option (Command reviewed) :=
  match state.phase with
  | .approve => if !locked state && !called state .approve then some .approve else none
  | .afterApprovalClock => some .afterApprovalClock
  | .revalidate =>
    if acknowledged state .approve && !locked state then some .revalidate else none
  | .beforeSignClock => some .beforeSignClock
  | .sign =>
    if acknowledged state .approve && acknowledged state .revalidate &&
        !called state .sign && !locked state then some .sign else none
  | .afterSignClock => some .afterSignClock
  | .reserve =>
    if acknowledged state .sign && !called state .reserve && !locked state then
      state.payload.map Command.reserve else none
  | .markExposed =>
    if acknowledged state .reserve && !called state .markExposed then
      state.payload.map Command.markExposed else none
  | .simulate =>
    if readyForExposure state && !called state .simulate && !called state .send then
      state.payload.map Command.simulate else none
  | .send =>
    if readyForExposure state && !called state .send &&
        (reviewed.flow == .direct || acknowledged state .simulate) then
      state.payload.map Command.send else none
  | .markSubmitted => state.payload.map Command.markSubmitted
  | .markUnknown => state.payload.map Command.markUnknown
  | .submitted | .unknown | .blocked => none

inductive Reply where
  | ok | failed | time (now : Nat) | signature (signed : Signed)
  | simulation (passed : Bool) | sent (response : Json)

private def fresh {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) (now : Nat) : Bool :=
  now >= reviewed.preparedAtMs && now - reviewed.preparedAtMs <= 300000

structure Decision {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) where
  private mk ::
  phase : Phase
  accepted : Bool
  payload : Option (FinalPayload reviewed)

def decideResponse {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (state : State reviewed) (command : Command reviewed) (reply : Reply) : Decision reviewed := Id.run do
  let mut phase := Phase.blocked
  let mut accepted := false
  let mut payload := state.payload
  match command, reply with
  | .approve, .ok => phase := .afterApprovalClock; accepted := true
  | .afterApprovalClock, .time now =>
    if fresh reviewed now then phase := .revalidate; accepted := true
  | .revalidate, .ok => phase := .beforeSignClock; accepted := true
  | .beforeSignClock, .time now =>
    if fresh reviewed now then phase := .sign; accepted := true
  | .sign, .signature signed =>
    if let .ok final := finalize reviewed signed then
      payload := some final; phase := .afterSignClock; accepted := true
  | .afterSignClock, .time now =>
    if fresh reviewed now then phase := .reserve; accepted := true
  | .reserve _, .ok => phase := .markExposed; accepted := true
  | .markExposed _, .ok =>
    phase := if reviewed.flow == .direct then .send else .simulate
    accepted := true
  | .simulate _, result =>
    phase := .markUnknown
    if let .simulation true := result then phase := .send; accepted := true
  | .send _, result =>
    phase := .markUnknown
    if let .sent json := result then
      if let .ok hash := Bundler.parseHash json then
        if hash == reviewed.hash then phase := .markSubmitted; accepted := true
  | .markSubmitted _, result =>
    phase := .markUnknown
    if let .ok := result then phase := .submitted; accepted := true
  | .markUnknown _, result =>
    phase := .unknown
    if let .ok := result then accepted := true
  | _, _ => pure ()
  return ⟨phase, accepted, payload⟩

/-- A callback exception can follow a completed external effect. Before
exposure it blocks; after exposure it requests unknown marking and never retries. -/
def respond {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (state : State reviewed) (reply : Reply) : State reviewed :=
  match next state with
  | none => state
  | some command =>
    let decision := decideResponse state command reply
    ⟨decision.phase, state.history ++ [⟨command.kind, decision.accepted⟩], decision.payload⟩

inductive Reachable {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) : State reviewed → Prop where
  | initial : Reachable reviewed (initial reviewed)
  | response {state : State reviewed} (prior : Reachable reviewed state) (reply : Reply) :
      Reachable reviewed (respond state reply)

/-- The reserve callback must acknowledge only after *all selected note paths*
contain this exact payload and authorization through exclusive protected writes.
markExposed similarly acknowledges its complete CAS update. No callback may
secretly expose signed material outside its designated simulation/send command.
These IO/OS contracts are explicit assumptions, not new Lean axioms. -/
structure Effects {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) where
  approve : String → IO Unit
  nowMs : IO Nat
  revalidate : IO Unit
  signDigest : ByteArray → IO Signed
  reserve : FinalPayload reviewed → IO Unit
  markExposed : ByteArray → IO Unit
  simulate : UserOperation → IO Bool
  rpc : JsonRpc.Method → Array Json → IO Json
  markSubmitted : ByteArray → IO Unit
  markUnknown : ByteArray → IO Unit

/-- Exactly one callback is invoked for each emitted instruction. Exceptions
become replies, including exceptions after signing, writing or broadcasting. -/
private def perform {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (effects : Effects reviewed) (command : Command reviewed) : IO Reply := do
  try
    match command with
    | .approve => effects.approve reviewed.text; return .ok
    | .afterApprovalClock | .beforeSignClock | .afterSignClock => return .time (← effects.nowMs)
    | .revalidate => effects.revalidate; return .ok
    | .sign => return .signature (← effects.signDigest reviewed.hash)
    | .reserve payload => effects.reserve payload; return .ok
    | .markExposed _ => effects.markExposed reviewed.hash; return .ok
    | .simulate payload => return .simulation (← effects.simulate payload.operation)
    | .send payload =>
      let destination ← match Bundler.address Bundler.entryPoint with
        | .ok value => pure value
        | .error _ => throw <| IO.userError "Invalid pinned EntryPoint."
      return .sent (← effects.rpc .sendUserOperation #[payload.json, toJson destination])
    | .markSubmitted _ => effects.markSubmitted reviewed.hash; return .ok
    | .markUnknown _ => effects.markUnknown reviewed.hash; return .ok
  catch _ => return .failed

structure Report {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) where
  private mk ::
  state : State reviewed
  reachable : Reachable reviewed state
  exhausted : Bool

private def runFuel {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (effects : Effects reviewed) : (fuel : Nat) → (state : State reviewed) →
    Reachable reviewed state → IO (Report reviewed)
  | 0, state, reachable => pure ⟨state, reachable, true⟩
  | fuel + 1, state, reachable => do
    match next state with
    | none => return ⟨state, reachable, false⟩
    | some command =>
      let reply ← perform effects command
      runFuel effects fuel (respond state reply) (.response reachable reply)

/-- This interpreter is the runnable CLI path, not a separate test model.
The finite machine has at most twelve callbacks; the extra fuel fails unknown. -/
def runWithTrace {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (effects : Effects reviewed) : IO (Report reviewed) :=
  runFuel effects 16 (initial reviewed) (.initial)

def runWith {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (effects : Effects reviewed) : IO Bundler.Outcome := do
  let report ← runWithTrace effects
  if report.state.phase == .blocked then
    throw <| IO.userError "Withdrawal stopped before executable exposure; keep any protected reservation."
  if !report.exhausted && report.state.phase == .submitted then
    return .submitted reviewed.hash
  return .unknown reviewed.hash

end Tornado.Runtime.WithdrawalDriver
