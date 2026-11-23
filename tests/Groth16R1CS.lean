import Tornado.Protocol.Groth16R1CS

open Lean Tornado.Protocol.Groth16R1CS

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check (json : Json) : Except String Nat := do
  let circuitHash ← (← json.getObjVal? "sourceCircuitSha256").getStr?
  let keyHash ← (← json.getObjVal? "sourceProvingKeySha256").getStr?
  require (circuitHash == "3ddd61dbff09caeec82d8edde95c674a3c34f9e66b1fe9f2c8783e72fe536f98")
    "Circuit source pin changed."
  require (keyHash == "8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af")
    "Proving-key source pin changed."
  let circuit ← decodeCircuit json
  let witness ← decodeWitness (← json.getObjVal? "witness")
  require (circuit.nVars == 28300 && circuit.nPublic == 6 && circuit.constraints.size == 28275)
    "Pinned Tornado R1CS dimensions changed."
  require (witness.size == 28300 && witness[0]! == 1)
    "Pinned public witness has wrong shape."
  require (witness[1]! == 340708282452592383170637552138375959003815801723242666430554919753685466375)
    "Pinned public Merkle root changed."
  require (witness[2]! == 14635895392245050583297764479838098008757573928940107190520237634208572819896)
    "Pinned public nullifier hash changed."
  let checked ← checkCircuit circuit witness
  require (checked == 28275) "Native R1CS checker skipped constraints."
  require ((checkCircuit circuit (witness.pop)).isOk == false)
    "Truncated witness was accepted."
  require ((checkCircuit circuit (witness.set! 0 0)).isOk == false)
    "Witness with zero constant slot was accepted."
  let changedRoot := witness.set! 1 ((witness[1]! + 1) % scalarPrime)
  require ((checkCircuit circuit changedRoot).isOk == false)
    "Altered public root still satisfied the pinned circuit."
  let malformed : LinearCombination := ⟨#[(witness.size, 1)]⟩
  require ((evaluateRow witness malformed).isOk == false)
    "Out-of-range signal index was accepted."
  return checked

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/groth16-tornado-r1cs.json"
  match Json.parse raw >>= check with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok checked =>
      IO.println s!"PASS: {checked} pinned Tornado R1CS constraints, public witness, and tamper checks"
      return 0
