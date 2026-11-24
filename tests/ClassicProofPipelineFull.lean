import Tornado.Protocol.ClassicProofPipeline
import Tornado.Domain.NoteIdentity

open Lean Tornado.Protocol.ClassicProofPipeline
open Tornado.Protocol.TornadoWitness Tornado.Protocol.Groth16R1CS
open Tornado.Crypto Tornado.Protocol.Groth16MSM

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def expectError (label : String) (value : Except String α) : IO Unit :=
  match value with
  | .ok _ => throw <| IO.userError s!"{label}: unexpectedly accepted"
  | .error _ => pure ()

private def bigEndian (n count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push ((n / 2 ^ (8 * (count - 1 - i)) % 256).toUInt8)
  return bytes

/-- All inputs in this test are public and intentionally unfunded. Fixed
    blinding values are for byte-for-byte oracle parity only. -/
def main : IO UInt32 := do
  let started ← IO.monoMsNow
  let compressedCircuit ← IO.FS.readBinFile
    "assets/proving/tornado-3ddd61dbff09caee.json.gz"
  let compressedKey ← IO.FS.readBinFile
    "assets/proving/tornadoProvingKey-8e2d2f22beafb5a9.bin.gz"
  let graphText ← IO.FS.readFile "fixtures/witness-vm-selected-components.json"
  let witnessCertificate ← IO.FS.readBinFile "assets/proving/tornado-witness-certificate-v1.json.gz"
  expectError "wrong graph digest" <|
    loadBundled compressedCircuit compressedKey (graphText ++ " ") witnessCertificate
  let assets ← unwrap "authenticate and decode bundled assets" <|
    loadBundled compressedCircuit compressedKey graphText witnessCertificate
  let key := bigEndian
    0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb 32
  let note ← unwrap "derive public note" <|
    tornadoSignatureNote key 1 0 0x199112eb461ea7eec1d75b33343542e1d069b41c
  let tree ← unwrap "build one-leaf tree" <| buildMimcTree #[note.commitment]
  let path ← unwrap "build public Merkle path" <| mimcProofAt tree 0
  let withdrawal : WithdrawalInput := {
    note, proof := path, expectedRoot := tree.root,
    recipient := 1, relayer := 0, fee := 0, refund := 0 }
  expectError "zero blinding" <| prove assets withdrawal 0 2
  expectError "out-of-field blinding" <| prove assets withdrawal
    Tornado.Protocol.BN254G1.scalarPrime 2
  let result ← unwrap "derive and verify native Classic proof" <|
    prove assets withdrawal 1 2
  let fixture ← unwrap "read public proof fixture" <|
    Json.parse (← IO.FS.readFile "fixtures/groth16-full-public-proof.json")
  let expectedHex ← unwrap "read public proof hex" <|
    (← unwrap "public fixture field" <| fixture.getObjVal? "solidityProofHex").getStr?
  let expectedSignals ← unwrap "read public signals" <|
    fixture.getObjVal? "publicSignals" >>= decodeWitness
  require (result.bytes.size == 256 &&
      "0x" ++ bytesToHex result.bytes == expectedHex &&
      result.signals == expectedSignals &&
      result.reviewed.signals == expectedSignals)
    "Native end-to-end proof or public signals differ from pinned SDK."
  expectError "wrong expected root" <| prove assets
    { withdrawal with expectedRoot := tree.root + 1 } 1 2
  let finished ← IO.monoMsNow
  IO.println s!"PASS: authenticated compressed assets, complete public witness, 256-byte SDK proof parity, and compiled-key pairing verification ({finished - started} ms)"
  return 0
