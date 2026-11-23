import Tornado.Runtime.Bundler

open Lean Tornado.Crypto Tornado.Protocol Tornado.Protocol.UserOperation08
open Tornado.Runtime Tornado.Runtime.Bundler

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def fails (action : IO α) : IO Bool := do
  try let _ ← action; return false
  catch _ => return true

def main : IO UInt32 := do
  let op : UserOperation := {
    sender := 1, verificationGasLimit := 50000, preVerificationGas := 100000,
    maxFeePerGas := 1000000000, maxPriorityFeePerGas := 100000000,
    signature := ⟨(Array.replicate 64 1).push 27⟩ }
  let json ← checked (encodeOperation op)
  require ((← checked <| (← checked (json.getObjVal? "sender")).getStr?) ==
    "0x0000000000000000000000000000000000000001") "Sender codec changed"
  require (!(validate { op with maxFeePerGas := 2 ^ 128 }).isOk)
    "Huge fee quote accepted"
  require (!(validate { op with preVerificationGas := 1000001 }).isOk)
    "Unbounded gas accepted"
  let reply := Json.mkObj [("verificationGasLimit", toJson "0xc350"),
    ("callGasLimit", toJson "0x0"), ("preVerificationGas", toJson "0x186a0")]
  let gas ← checked (parseEstimate reply op)
  require (gas.verificationGasLimit == 50000 && gas.callGasLimit == 0)
    "Bounded estimate changed"
  require (!(parseEstimate (reply.setObjVal! "callGasLimit" (toJson "0x80000000")) op).isOk)
    "Malicious gas estimate accepted"
  let auth : Authorization := {
    chainId := 1, delegate := 0xe6cae83bde06e4c305530e199d7217f42808555b,
    nonce := 0, r := 1, s := 1, yParity := 0 }
  let marked := { op with
    factory := some .eip7702Marker
    authorizationAddress := some auth.delegate }
  require (!(withAuthorization 1 marked none).isOk &&
    !(withAuthorization 11155111 marked (some auth)).isOk &&
    !(withAuthorization 1 marked (some { auth with delegate := 9 })).isOk)
    "Missing or mismatched authorization accepted"
  let authorized ← checked (withAuthorization 1 marked (some auth))
  require ((authorized.getObjVal? "eip7702Auth").isOk)
    "Authorization disappeared from the exact transport payload"
  let expected ← checked (userOperationHash 1 entryPoint op)
  let events ← IO.mkRef (#[] : Array String)
  let effects : Effects := {
    rpc := fun method _ => do
      require (method == .sendUserOperation) "Unexpected bundler method"
      events.modify (·.push "send")
      return toJson (dataHex expected)
    reserve := fun hash bytes => do
      require (hash == expected && !bytes.isEmpty) "Wrong reserved payload"
      events.modify (·.push "reserve")
    markExposed := fun _ => events.modify (·.push "exposed")
    markSubmitted := fun _ => events.modify (·.push "submitted")
    markUnknown := fun _ => events.modify (·.push "unknown") }
  match ← submitWith effects 1 op with
  | .submitted hash => require (hash == expected) "Changed operation hash"
  | .unknown _ => throw <| IO.userError "Valid operation rejected"
  require ((← events.get) == #["reserve", "exposed", "send", "submitted"])
    "Journal did not precede network exposure"
  events.set #[]
  require (← fails <| submitWith { effects with reserve := fun _ _ => do
    throw <| IO.userError "Injected disk failure" } 1 op)
    "Failed reservation did not stop submission"
  require (← events.get <&> Array.isEmpty) "Network ran after failed reservation"
  match ← submitWith { effects with rpc := fun _ _ => do
    events.modify (·.push "send")
    throw <| IO.userError "Injected lost reply" } 1 op with
  | .unknown hash => require (hash == expected) "Lost recoverable hash"
  | _ => throw <| IO.userError "Lost reply became a successful submission"
  require ((← events.get) == #["reserve", "exposed", "send", "unknown"])
    "Ambiguous send retried or lost journal state"
  events.set #[]
  match ← submitWith { effects with rpc := fun _ _ => pure (toJson
    (dataHex (⟨Array.replicate 32 0⟩ : ByteArray))) } 1 op with
  | .unknown _ => pure ()
  | _ => throw <| IO.userError "Wrong returned hash accepted"
  IO.println "PASS: bounded bundler codec and estimates, durable exposure order, and ambiguous-send stop"
  return 0
