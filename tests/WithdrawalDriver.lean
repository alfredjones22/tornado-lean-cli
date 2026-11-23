import Tornado.Runtime.WithdrawalDriver
import Tornado.Protocol.Rlp

open Lean Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Runtime.WithdrawalDriver

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def key : ByteArray := ⟨(Array.replicate 31 0).push 1⟩
private def number (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def operation (owner : Nat) : UserOperation := {
  sender := owner, verificationGasLimit := 50000, preVerificationGas := 100000,
  maxFeePerGas := 1000000000, maxPriorityFeePerGas := 100000000 }

private def signer {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned) : IO Signed := do
  let signature := (← checked <| secp256k1SignDigest key reviewed.hash).bytes65
  let authorization ← match reviewed.flow with
    | .batch => pure none
    | .direct => do
      let delegate := 0xe6cae83bde06e4c305530e199d7217f42808555b
      let digest ← checked <| Rlp.authorizationHash7702 reviewed.chainId delegate 0
      let auth ← checked <| secp256k1SignDigest key digest
      pure <| some {
        chainId := reviewed.chainId, delegate, nonce := 0,
        r := auth.r, s := auth.s, yParity := if auth.recovery == 0 then 0 else 1 }
  return { owner := reviewed.owner, signature, authorization }

structure Faults where
  fail : Option Kind := none
  staleClock : Option Nat := none
  partialReserve : Bool := false
  ambiguousMark : Bool := false
  simulationRejected : Bool := false
  wrongHash : Bool := false
  deriving Inhabited

private def scenario {unsigned : UserOperation} (reviewed : ReviewedOperation unsigned)
    (signed : Signed) (faults : Faults := {}) :
    IO (Report reviewed × List Kind × Array (Option ByteArray)) := do
  let callbacks ← IO.mkRef ([] : List Kind)
  let claims ← IO.mkRef (Array.replicate reviewed.selected.size (none : Option ByteArray))
  let marked ← IO.mkRef false
  let clocks ← IO.mkRef 0
  let enter (kind : Kind) : IO Unit := do
    callbacks.modify (· ++ [kind])
    if faults.fail == some kind then throw <| IO.userError "Injected callback failure after possible effect."
  let exactClaims (payload : FinalPayload reviewed) : IO Unit := do
    require ((← claims.get).all (· == some payload.bytes) && (← marked.get))
      "Executable payload escaped before every exact claim and exposure mark."
    require (payload.bytes == payload.json.compress.toUTF8 &&
      (← checked <| Bundler.withAuthorization reviewed.chainId payload.operation signed.authorization) == payload.json)
      "Final JSON or separate authorization changed before exposure."
  let effects : Effects reviewed := {
    approve := fun text => do
      require (text == reviewed.text) "Approval rendered different intent."
      enter .approve,
    nowMs := do
      let index ← clocks.get
      clocks.set (index + 1)
      enter (if index == 0 then .afterApprovalClock else if index == 1 then .beforeSignClock else .afterSignClock)
      return if faults.staleClock == some index then reviewed.preparedAtMs + 300001
        else reviewed.preparedAtMs,
    revalidate := enter .revalidate,
    signDigest := fun digest => do
      require (digest == reviewed.hash) "A different digest was sent to the signer."
      enter .sign
      return signed,
    reserve := fun payload => do
      enter .reserve
      for i in [0:reviewed.selected.size] do
        require ((← claims.get)[i]!.isNone) "Permanent claim was overwritten."
        claims.modify (·.set! i (some payload.bytes))
        if faults.partialReserve then throw <| IO.userError "Ambiguous partial note claim.",
    markExposed := fun hash => do
      require (hash == reviewed.hash) "Exposure marker changed operation."
      enter .markExposed
      marked.set true
      if faults.ambiguousMark then throw <| IO.userError "Exposure marker write reply lost.",
    simulate := fun candidate => do
      enter .simulate
      let payload ← checked <| finalize reviewed signed
      require ((← checked <| Bundler.encodeOperation candidate) ==
        (← checked <| Bundler.encodeOperation payload.operation)) "Simulation changed executable operation."
      exactClaims payload
      return !faults.simulationRejected,
    rpc := fun method params => do
      enter .send
      let payload ← checked <| finalize reviewed signed
      exactClaims payload
      require (method == .sendUserOperation && params ==
        #[payload.json, toJson (← checked <| Bundler.address Bundler.entryPoint)])
        "RPC method or exact authorized request bytes changed."
      return toJson (Bundler.dataHex (if faults.wrongHash then ⟨Array.replicate 32 0⟩ else reviewed.hash)),
    markSubmitted := fun hash => do
      require (hash == reviewed.hash) "Submitted marker changed operation."
      enter .markSubmitted,
    markUnknown := fun hash => do
      require (hash == reviewed.hash) "Unknown marker lost reserved operation."
      enter .markUnknown }
  let result ← runWithTrace effects
  let actual ← callbacks.get
  require (result.state.history.map (·.kind) == actual)
    "The runtime report differs from the actual callback invocation trace."
  require (!result.exhausted && actual.count .sign <= 1 && actual.count .send <= 1 &&
    actual.count .simulate <= 1) "A callback repeated or the finite machine exhausted its budget."
  return (result, actual, ← claims.get)

private def checkUnknown {unsigned : UserOperation} {reviewed : ReviewedOperation unsigned}
    (result : Report reviewed) : IO Unit := do
  require (result.state.phase == .unknown && (next result.state).isNone)
    "An uncertain attempt did not become terminal."
  for reply in [Reply.ok, .failed, .time 0, .simulation true, .sent (toJson ("0x0" : String))] do
    let after := respond result.state reply
    require (after.history == result.state.history && (next after).isNone)
      "A delayed or fabricated reply restarted a terminal unknown candidate."

def main : IO UInt32 := do
  let owner := number (← checked <| secp256k1EthereumAddress key)
  let unsigned := operation owner
  for flow in [Flow.direct, .batch] do
    let selected := if flow == .direct then #[NoteId.mk 1 11]
      else #[NoteId.mk 1 11, NoteId.mk 2 22]
    let reviewed ← checked <| prepareReviewed 1 owner unsigned selected flow 1000 "Exact public fixture review."
    let signed ← signer reviewed
    let payload ← checked <| finalize reviewed signed
    require (payload.bytes == (← checked <| Bundler.withAuthorization 1
      { unsigned with signature := signed.signature } signed.authorization).compress.toUTF8)
      "Finalized payload differs from exact reviewed operation plus signature/auth."
    require (!(finalize reviewed { signed with owner := owner + 1 }).isOk &&
      !(finalize reviewed { signed with signature := ⟨Array.replicate 65 0⟩ }).isOk)
      "Wrong owner or malformed signature entered an executable payload."
    for rejected in [{ signed with owner := owner + 1 },
        { signed with signature := ⟨Array.replicate 65 0⟩ }] do
      let (result, trace, claims) ← scenario reviewed rejected
      require (result.state.phase == .blocked && !trace.contains .reserve &&
        !trace.contains .send && claims.all Option.isNone)
        "Rejected signer output reached reservation or executable disclosure."
    if let some auth := signed.authorization then
      for changed in [{ auth with nonce := 1 }, { auth with delegate := 9 },
          { auth with chainId := 11155111 }] do
        require (!(finalize reviewed { signed with authorization := some changed }).isOk)
          "Changed separate authorization survived a matching UserOperation hash."
      require (!(finalize reviewed { signed with authorization := none }).isOk)
        "A missing direct authorization was accepted."
    else
      require (!(finalize reviewed { signed with authorization := some {
        chainId := 1, delegate := 9, nonce := 0, r := 1, s := 1, yParity := 0 } }).isOk)
        "Batch execution accepted an unexpected authorization."
    let (valid, trace, claims) ← scenario reviewed signed
    require (valid.state.phase == .submitted && claims.all Option.isSome &&
      trace == [.approve, .afterApprovalClock, .revalidate, .beforeSignClock, .sign,
        .afterSignClock, .reserve, .markExposed] ++
        (if flow == .batch then [.simulate] else []) ++ [.send, .markSubmitted])
      "Successful callback order or all-note reservations changed."
    for kind in [Kind.approve, .afterApprovalClock, .revalidate, .beforeSignClock,
        .sign, .afterSignClock, .reserve, .markExposed] do
      let (result, trace, _) ← scenario reviewed signed { fail := some kind }
      require (result.state.phase == .blocked && !trace.contains .send && !trace.contains .simulate)
        "A pre-exposure callback failure permitted executable disclosure."
    for index in [0, 1, 2] do
      let (result, trace, _) ← scenario reviewed signed { staleClock := some index }
      require (result.state.phase == .blocked && !trace.contains .reserve && !trace.contains .send)
        "An expired approval reached reservation or network exposure."
    let (partialClaim, partialTrace, partialClaims) ← scenario reviewed signed { partialReserve := true }
    require (partialClaim.state.phase == .blocked && partialClaims[0]!.isSome &&
      !partialTrace.contains .markExposed && !partialTrace.contains .send)
      "A partial claim was released or exposed a payload."
    let (ambiguousMark, trace, _) ← scenario reviewed signed { ambiguousMark := true }
    require (ambiguousMark.state.phase == .blocked && !trace.contains .send && !trace.contains .simulate)
      "An ambiguous exposure marker permitted a network call."
    for faults in [({ fail := some .send } : Faults), { wrongHash := true },
        { fail := some .markSubmitted }] do
      let (unknown, trace, saved) ← scenario reviewed signed faults
      checkUnknown unknown
      require (trace.count .send == 1 && saved.all Option.isSome)
        "Unknown outcome duplicated a send or released a note claim."
    let (failedUnknownWrite, _, _) ← scenario reviewed signed { fail := some .markUnknown, wrongHash := true }
    checkUnknown failedUnknownWrite
    if flow == .batch then
      for faults in [({ simulationRejected := true } : Faults), { fail := some .simulate }] do
        let (unknown, trace, saved) ← scenario reviewed signed faults
        checkUnknown unknown
        require (!trace.contains .send && trace.count .simulate == 1 && saved.all Option.isSome)
          "Failed signed simulation allowed a send, retry or claim release."
  IO.println "PASS: runnable withdrawal machine, exact reviewed payload, callback fault traces and terminal uncertainty"
  return 0
