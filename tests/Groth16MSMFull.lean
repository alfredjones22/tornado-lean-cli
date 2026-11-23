import Tornado.Protocol.Groth16MSM
import Tornado.Domain.NoteIdentity

open Lean Tornado.Protocol.Groth16MSM Tornado.Protocol.ProvingKey
open Tornado.Protocol.WitnessVM Tornado.Protocol.TornadoWitness
open Tornado.Protocol.Groth16R1CS Tornado.Crypto

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw <| IO.userError s!"{label}: {error}"

private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError label

private def bigEndian (n count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push ((n / 2 ^ (8 * (count - 1 - i)) % 256).toUInt8)
  return bytes

/-- Optional public-only full-key test. The caller supplies the decompressed
    *public* pinned proving key; the parser authenticates its exact SHA-256.
    Fixed r=1 and s=2 are test vectors, never production blinding values. -/
def main (args : List String) : IO UInt32 := do
  let [path] := args | throw <| IO.userError "Expected public key path."
  let started ← IO.monoMsNow
  let pinnedKey ← unwrap "authenticate public proving key" <|
    authenticatePinnedKey (← IO.FS.readBinFile path)
  let graph ← unwrap "authenticate public arithmetic graph" <|
    decodePinnedGraph (← IO.FS.readFile "fixtures/witness-vm-selected-components.json")
  let fixture ← unwrap "parse public R1CS fixture" <|
    Json.parse (← IO.FS.readFile "fixtures/groth16-tornado-r1cs.json")
  let circuit ← unwrap "authenticate public R1CS" <|
    authenticatePinnedCircuit (← unwrap "parse public R1CS" <| decodeCircuit fixture)
  let key := bigEndian
    0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb 32
  let note ← unwrap "derive public note" <|
    tornadoSignatureNote key 1 0 0x199112eb461ea7eec1d75b33343542e1d069b41c
  let tree ← unwrap "build public one-leaf tree" <| buildMimcTree #[note.commitment]
  let pathProof ← unwrap "build public Merkle path" <| mimcProofAt tree 0
  let withdrawal : WithdrawalInput := {
    note, proof := pathProof, expectedRoot := tree.root,
    recipient := 1, relayer := 0, fee := 0, refund := 0 }
  let inputs ← unwrap "prepare public witness inputs" <| prepareInputPrefix withdrawal
  let result ← unwrap "derive checked proof points" <|
    deriveCheckedProofPoints pinnedKey graph circuit inputs note.commitment 1 2
  let fixtureWitness ← unwrap "parse expected public witness" <|
    fixture.getObjVal? "witness" >>= decodeWitness
  require (result.witness == fixtureWitness)
    "Full native witness differs from the pinned public SDK witness."
  let bytes ← unwrap "serialize Solidity proof" <| solidityProofBytes result.points
  let expected ← unwrap "parse public proof oracle" <|
    Json.parse (← IO.FS.readFile "fixtures/groth16-full-public-proof.json")
  let expectedSignals ← unwrap "read SDK public signals" <|
    expected.getObjVal? "publicSignals" >>= decodeWitness
  require (result.points.publicSignals == expectedSignals)
    "Full native public signals differ from the pinned SDK oracle."
  let expectedHex ← unwrap "read expected proof bytes" <|
    (← unwrap "proof fixture field" <| expected.getObjVal? "solidityProofHex").getStr?
  let expectedSHA ← unwrap "read expected proof digest" <|
    (← unwrap "proof digest field" <| expected.getObjVal? "solidityProofSHA256").getStr?
  require (bytes.size == 256 && "0x" ++ bytesToHex bytes == expectedHex &&
    sha256Hex bytes == expectedSHA)
    "Full native proof bytes differ from the pinned SDK oracle."
  let finished ← IO.monoMsNow
  IO.println s!"PASS: native full public Groth16 proof bytes match pinned SDK oracle ({finished - started} ms)"
  return 0
