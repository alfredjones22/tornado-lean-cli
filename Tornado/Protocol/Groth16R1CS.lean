import Lean

/-!
A native BN254 scalar-field R1CS checker for the pinned Tornado circuit.
This checks a complete witness against every algebraic constraint. It does not
generate the witness or a Groth16 proof, nor verify elliptic-curve pairings.
-/

namespace Tornado.Protocol.Groth16R1CS

open Lean

/-- BN254 scalar-field order (`Fr`), distinct from the base-field order. -/
def scalarPrime : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

structure LinearCombination where
  terms : Array (Nat × Nat)
  deriving Inhabited

structure Constraint where
  a : LinearCombination
  b : LinearCombination
  c : LinearCombination
  deriving Inhabited

structure Circuit where
  nVars : Nat
  nPublic : Nat
  constraints : Array Constraint
  deriving Inhabited

private def decimalNat (raw : String) : Except String Nat := do
  if raw.isEmpty || !raw.toList.all Char.isDigit then throw "Expected an unsigned decimal integer."
  let some value := raw.toNat? | throw "Expected an unsigned decimal integer."
  return value

/-- Decode a Circom JSON constraint row exactly as a sparse signal-index to
    field-coefficient object. Reject malformed or out-of-field entries. -/
def decodeLinearCombination (json : Json) : Except String LinearCombination := do
  let object ← json.getObj?
  let mut terms := #[]
  for (key, value) in object.toList do
    let index ← decimalNat key
    let coefficient ← decimalNat (← value.getStr?)
    if coefficient >= scalarPrime then throw "R1CS coefficient is outside BN254 Fr."
    terms := terms.push (index, coefficient)
  return ⟨terms⟩

def decodeConstraint (json : Json) : Except String Constraint := do
  let rows ← json.getArr?
  if rows.size != 3 then throw "R1CS constraint must have A, B, and C rows."
  return ⟨(← decodeLinearCombination rows[0]!),
    (← decodeLinearCombination rows[1]!),
    (← decodeLinearCombination rows[2]!)⟩

/-- Parse the native constraint subset of the pinned Circom circuit JSON.
    Templates and signal scheduling are deliberately outside this checker. -/
def decodeCircuit (json : Json) : Except String Circuit := do
  let nVars ← (← json.getObjVal? "nVars").getNat?
  let nPubInputs ← (← json.getObjVal? "nPubInputs").getNat?
  let nOutputs ← (← json.getObjVal? "nOutputs").getNat?
  let rows ← (← json.getObjVal? "constraints").getArr?
  if nVars == 0 || nVars > 100000 || rows.size > 100000 ||
      nPubInputs + nOutputs >= nVars then
    throw "R1CS circuit dimensions are invalid."
  let mut constraints := #[]
  for row in rows do constraints := constraints.push (← decodeConstraint row)
  return ⟨nVars, nPubInputs + nOutputs, constraints⟩

def decodeWitness (json : Json) : Except String (Array Nat) := do
  let values ← json.getArr?
  let mut witness := #[]
  for value in values do
    let element ← decimalNat (← value.getStr?)
    if element >= scalarPrime then throw "R1CS witness value is outside BN254 Fr."
    witness := witness.push element
  return witness

def rowIndicesValid (witness : Array Nat) (row : LinearCombination) : Bool :=
  row.terms.all (fun (index, coefficient) =>
    index < witness.size && coefficient < scalarPrime)

/-- Evaluate a sparse linear combination in BN254 Fr. The bound check
    precedes all array indexing; malformed constraints fail closed. -/
def evaluateRow (witness : Array Nat) (row : LinearCombination) : Except String Nat :=
  if rowIndicesValid witness row then
    .ok ((row.terms.foldl (fun acc (index, coefficient) =>
      acc + coefficient * witness[index]!) 0) % scalarPrime)
  else .error "R1CS signal index or coefficient is invalid."

/-- The exact R1CS identity `(A·w)(B·w) = C·w (mod Fr)`. -/
def checkConstraint (witness : Array Nat) (constraint : Constraint) : Except String Bool :=
  match evaluateRow witness constraint.a with
  | .error error => .error error
  | .ok a =>
    match evaluateRow witness constraint.b with
    | .error error => .error error
    | .ok b =>
      match evaluateRow witness constraint.c with
      | .error error => .error error
      | .ok c => .ok ((a * b) % scalarPrime == c)

/-- Check shape, field bounds, constant-one witness slot, and every equation.
    The returned count is the number of constraints checked. -/
def checkCircuit (circuit : Circuit) (witness : Array Nat) : Except String Nat := do
  if witness.size != circuit.nVars then throw "R1CS witness length differs from the circuit."
  if witness[0]? != some 1 then throw "R1CS witness constant slot must equal one."
  if witness.any (fun value => value >= scalarPrime) then
    throw "R1CS witness value is outside BN254 Fr."
  for i in [0:circuit.constraints.size] do
    if !(← checkConstraint witness circuit.constraints[i]!) then
      throw s!"R1CS constraint {i} failed."
  return circuit.constraints.size

/-- A successful row evaluation has passed every native index/field guard. -/
theorem evaluated_row_has_valid_indices (witness : Array Nat)
    (row : LinearCombination) (result : Nat)
    (h : evaluateRow witness row = .ok result) :
    rowIndicesValid witness row = true := by
  cases hv : rowIndicesValid witness row with
  | false => simp [evaluateRow, hv] at h
  | true => simp

/-- A successful constraint check certifies the exact native Fr equation over
    its three evaluated linear combinations. -/
theorem checked_constraint_satisfies (witness : Array Nat)
    (constraint : Constraint)
    (h : checkConstraint witness constraint = .ok true) :
    ∃ a b c, evaluateRow witness constraint.a = .ok a ∧
      evaluateRow witness constraint.b = .ok b ∧
      evaluateRow witness constraint.c = .ok c ∧
      (a * b) % scalarPrime = c := by
  cases ha : evaluateRow witness constraint.a with
  | error error => simp [checkConstraint, ha] at h
  | ok a =>
    cases hb : evaluateRow witness constraint.b with
    | error error => simp [checkConstraint, ha, hb] at h
    | ok b =>
      cases hc : evaluateRow witness constraint.c with
      | error error => simp [checkConstraint, ha, hb, hc] at h
      | ok c =>
        simp [checkConstraint, ha, hb, hc] at h
        exact ⟨a, b, c, rfl, rfl, rfl, h⟩

end Tornado.Protocol.Groth16R1CS

#print axioms Tornado.Protocol.Groth16R1CS.evaluated_row_has_valid_indices
#print axioms Tornado.Protocol.Groth16R1CS.checked_constraint_satisfies
