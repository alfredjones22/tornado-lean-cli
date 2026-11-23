import Tornado.Protocol.ProverWorkerWire

open Lean Tornado.Protocol.ProverWorkerWire

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def rejectRequest (label raw : String) : IO Unit :=
  match Request.decode raw with
  | .ok _ => throw <| IO.userError s!"{label}: accepted malformed request"
  | .error message =>
    require (message == "Invalid prover worker request")
      s!"{label}: unexpected error disclosure"

private def rejectResult (label raw : String) : IO Unit :=
  match Result.decode raw with
  | .ok _ => throw <| IO.userError s!"{label}: accepted malformed result"
  | .error message =>
    require (message == "Invalid prover worker result")
      s!"{label}: unexpected error disclosure"

def main : IO UInt32 := do
  let request : Request := {
    chainId := 1
    pool := 0x199112eb461ea7eec1d75b33343542e1d069b41c
    commitment := 1
    nullifierHash := 2
    leafIndex := 0
    root := 3
    siblings := Array.replicate 20 4
    pathIndices := Array.replicate 20 0
    recipient := 5
    relayer := 0
    fee := 0
    refund := 0 }
  let raw := request.encode
  let decoded ← unwrap "roundtrip request" <| Request.decode raw
  require (decoded == request && raw.toUTF8.size < 4096)
    "Public request failed canonical roundtrip"
  require (request.publicSignals == #[3, 2, 5, 0, 0, 0] &&
      request.hash.size == 32) "Public signal order or request hash changed"
  rejectRequest "extra secret field" <|
    (request.toJson.setObjVal! "notePreimage" (Lean.toJson "private")).compress
  rejectRequest "extra public field" <|
    (request.toJson.setObjVal! "unused" (Lean.toJson "x")).compress
  rejectRequest "duplicate field" <|
    raw.replace "\"chainId\":\"1\"" "\"chainId\":\"1\",\"chainId\":\"1\""
  rejectRequest "leading zero" <|
    raw.replace "\"chainId\":\"1\"" "\"chainId\":\"01\""
  rejectRequest "trailing newline" (raw ++ "\n")
  rejectRequest "overlong input" (String.ofList (List.replicate 4097 'x'))
  rejectRequest "out-of-range chain" <|
    (Request.encode { request with chainId := 2 ^ 64 })
  rejectRequest "out-of-range commitment" <|
    (Request.encode { request with commitment := Tornado.Protocol.BN254G1.scalarPrime })
  rejectRequest "out-of-range nullifier hash" <|
    (Request.encode { request with nullifierHash := Tornado.Protocol.BN254G1.scalarPrime })
  rejectRequest "short Merkle path" <|
    (Request.encode { request with siblings := Array.replicate 19 4 })
  rejectRequest "wrong path direction" <|
    (Request.encode { request with pathIndices := #[1] ++ Array.replicate 19 0 })
  rejectRequest "wrong leaf index" <|
    (Request.encode { request with leafIndex := 2 ^ 20 })
  let proof : ByteArray := ⟨Array.replicate 256 0⟩
  let result : Result := {
    requestHash := request.hash
    proof
    signals := request.publicSignals }
  let resultRaw := result.encode
  let resultDecoded ← unwrap "roundtrip result" <| Result.decode resultRaw
  require (resultDecoded == result && resultRaw.toUTF8.size < 2048)
    "Public result failed canonical roundtrip"
  let _ ← unwrap "bind result" <| Result.validateFor request resultDecoded
  rejectResult "extra secret result field" <|
    (result.toJson.setObjVal! "note" (Lean.toJson "private")).compress
  rejectResult "duplicate result field" <|
    resultRaw.replace "\"version\":1" "\"version\":1,\"version\":1"
  rejectResult "bad proof length" <|
    (Result.encode { result with proof := proof.extract 0 255 })
  rejectResult "out-of-range signal" <|
    (Result.encode { result with signals := #[3, 2, 5, 0, 0,
      Tornado.Protocol.BN254G1.scalarPrime] })
  rejectResult "noncanonical hex" <|
    resultRaw.replace "0x" "0X"
  require (!(Result.validateFor request
      { result with signals := #[3, 2, 6, 0, 0, 0] }).isOk)
    "Changed public signal was accepted"
  require (!(Result.validateFor request
      { result with requestHash := ⟨Array.replicate 32 0⟩ }).isOk)
    "Changed request hash was accepted"
  IO.println "PASS: strict public prover worker wire and request/result binding"
  return 0
