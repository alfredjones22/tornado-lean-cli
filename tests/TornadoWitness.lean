import Tornado.Protocol.TornadoWitness

open Lean Tornado.Crypto Tornado.Protocol.TornadoWitness
open Tornado.Protocol.Groth16R1CS

private def bigEndian (n count : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:count] do
    result := result.push ((n / 2 ^ (8 * (count - 1 - i)) % 256).toUInt8)
  return result

private def unwrap (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{label}: {error}"

private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError label

private def rejected (result : Except String α) : Bool := !result.isOk

def main : IO UInt32 := do
  -- The public mnemonic "abandon" x23 + "art" yields this test-only signer.
  -- All note, Pedersen, and MiMC operations below execute natively in Lean.
  let key := bigEndian
    0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb 32
  let note ← unwrap "derive test note" <|
    tornadoSignatureNote key 1 0 0x199112eb461ea7eec1d75b33343542e1d069b41c
  let tree ← unwrap "build one-leaf Tornado tree" <|
    buildMimcTree #[note.commitment]
  let proof ← unwrap "build membership path" <| mimcProofAt tree 0
  let input : WithdrawalInput := {
    note, proof, expectedRoot := tree.root,
    recipient := 1, relayer := 0, fee := 0, refund := 0
  }
  let inputSignals ← unwrap "prepare 49 input signals" <| prepareInputPrefix input
  require (inputSignals.size == 49) "Tornado input prefix does not have 49 slots."

  -- This fixture is a full SDK-generated witness for precisely these public
  -- test inputs. Compare all 49 slots, including the public six.
  let raw ← IO.FS.readFile "fixtures/groth16-tornado-r1cs.json"
  let fixture ← unwrap "parse pinned witness fixture" <| Json.parse raw
  let circuitHash ← unwrap "read fixture circuit pin" <|
    (fixture.getObjVal? "sourceCircuitSha256" >>= Json.getStr?)
  require (circuitHash ==
    "3ddd61dbff09caeec82d8edde95c674a3c34f9e66b1fe9f2c8783e72fe536f98")
    "Pinned Tornado circuit hash changed."
  let witness ← unwrap "decode full fixture witness" <|
    fixture.getObjVal? "witness" >>= decodeWitness
  require (witness.size == 28300) "Pinned Tornado witness length changed."
  for i in [0:49] do
    require (inputSignals[i]! == witness[i]!) s!"Native input slot {i} differs from SDK witness."

  require (rejected (prepareInputPrefix { input with expectedRoot := tree.root + 1 }))
    "An unexpected pool root was accepted."
  require (rejected (prepareInputPrefix { input with recipient := 2 ^ 160 }))
    "An oversized recipient was accepted."
  require (rejected (prepareInputPrefix { input with fee := scalarPrime }))
    "An out-of-field fee was accepted."
  require (rejected (prepareInputPrefix { input with proof :=
    { proof with siblings := proof.siblings.pop } }))
    "A short Merkle path was accepted."
  require (rejected (prepareInputPrefix { input with note :=
    { note with commitment := note.commitment + 1 } }))
    "A forged note commitment was accepted."
  require (rejected (prepareInputPrefix { input with note :=
    { note with nullifierHash := note.nullifierHash + 1 } }))
    "A forged nullifier hash was accepted."
  require (rejected (prepareInputPrefix { input with proof :=
    { proof with siblings := proof.siblings.set! 0 (proof.siblings[0]! + 1) } }))
    "A forged Merkle sibling was accepted."
  require (rejected (prepareInputPrefix { input with proof :=
    { proof with pathIndices := proof.pathIndices.set! 0 1 } }))
    "A forged Merkle direction was accepted."
  IO.println "PASS: native Lean generated all 49 pinned Tornado witness input slots; eight tamper cases rejected"
  return 0
