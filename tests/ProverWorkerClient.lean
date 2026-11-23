import Lean
import Tornado.Runtime.ProverWorkerClient
import Tornado.Crypto.TornadoSignature
import Tornado.Crypto.MiMCTree
import Tornado.Domain.Catalog

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol
open Tornado.Protocol.ProverWorkerWire
open Tornado.Runtime.ProverWorkerClient

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def word (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do
    bytes := bytes.push ((value / 256 ^ (31 - i) % 256).toUInt8)
  return bytes

/-- This fixture key/note is public and unfunded. It is used only to recover
    the exact path/commitment of the pinned public SDK proof. -/
private def fixtureKey : ByteArray := word
  0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb

def main : IO UInt32 := do
  let started ← IO.monoMsNow
  let some pool := poolFor .mainnet "0.01" "ETH"
    | throw <| IO.userError "Missing public fixture pool."
  let poolBytes ← unwrap "fixture pool" <| parseHexBytes pool.address
  let poolNat := poolBytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let note ← unwrap "public fixture note" <|
    tornadoSignatureNote fixtureKey 1 0 poolNat
  let tree ← unwrap "public fixture tree" <| buildMimcTree #[note.commitment]
  let path ← unwrap "public fixture path" <| mimcProofAt tree 0
  let request : Request := {
    chainId := 1, pool := poolNat,
    commitment := note.commitment,
    nullifierHash := note.nullifierHash,
    leafIndex := 0, root := tree.root,
    siblings := path.siblings, pathIndices := path.pathIndices,
    recipient := 1, relayer := 0, fee := 0, refund := 0 }
  let _ ← unwrap "valid public worker request" request.validate
  let fixture ← unwrap "public SDK proof fixture" <|
    Json.parse (← IO.FS.readFile "fixtures/groth16-full-public-proof.json")
  let rawProof ← unwrap "fixture proof field" <|
    (← unwrap "proof field" <| fixture.getObjVal? "solidityProofHex").getStr?
  let proofBytes ← unwrap "fixture proof bytes" <| parseHexBytes rawProof
  let rawSignals ← unwrap "fixture signals" <|
    (← unwrap "signal field" <| fixture.getObjVal? "publicSignals").getArr?
  let signals ← rawSignals.mapM fun item => do
    let text ← unwrap "signal text" item.getStr?
    let some number := text.toNat?
      | throw <| IO.userError "Invalid public fixture signal."
    return number
  require (signals == request.publicSignals)
    "Pinned public SDK signals differ from the reviewed request."
  let result : Result := {
    requestHash := request.hash, proof := proofBytes, signals := signals }
  let accepted ← unwrap "valid public worker response" <|
    acceptResponse request result
  require (accepted.signals == request.publicSignals &&
    accepted.proofBytes == proofBytes &&
    accepted.calldata.size == 516 &&
    accepted.calldata.extract 260 516 == proofBytes)
    "Accepted public proof or Classic calldata differs from the fixture."
  let wrongHash := { result with requestHash := result.requestHash.set! 0 0xff }
  require (!(acceptResponse request wrongHash).isOk)
    "A changed public request hash was accepted."
  require (!(acceptResponse { request with recipient := 2 } result).isOk)
    "A response was rebound to a changed recipient."
  for i in [0:6] do
    let changed := { result with signals := signals.set! i (signals[i]! + 1) }
    require (!(acceptResponse request changed).isOk)
      s!"A changed Classic public signal {i} was accepted."
  require (!(decodeProof (proofBytes.extract 0 255)).isOk)
    "A truncated Solidity proof was accepted."
  require (!(decodeProof (proofBytes.set! 0 0xff)).isOk)
    "An out-of-field proof coordinate was accepted."
  require (!(acceptResponse request
    { result with proof := proofBytes.set! 0 0xff }).isOk)
    "An out-of-field worker proof was accepted."
  let finished ← IO.monoMsNow
  IO.println s!"PASS: prover worker public response binding, strict proof decoding, and compiled-key verification ({finished - started} ms)"
  return 0
