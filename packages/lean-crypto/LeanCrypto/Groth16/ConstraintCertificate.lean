import LeanCrypto.Groth16.FFT
import LeanCrypto.Groth16.R1CS

/-! Public-data constraint certificates. Sparse expressions use slot zero
as the constant-one variable. This module never receives secret witnesses.
The mathematical soundness interpretation is in the proof workspace. -/

namespace LeanCrypto.Groth16.ConstraintCertificate

abbrev Linear := List (Nat × Nat)
abbrev Monomial := Nat × Nat
abbrev Quadratic := List (Monomial × Nat)

structure Equation where
  a : Linear
  b : Linear
  c : Linear
  deriving Inhabited, Repr, DecidableEq

structure Match where
  source : Nat
  scale : Nat
  deriving Inhabited, Repr, DecidableEq

inductive LinearStep where
  | scale (source scalar : Nat)
  | add (left right : Nat)
  deriving Inhabited, Repr, DecidableEq

structure Rule where
  pivot : Nat
  row : Nat
  deriving Inhabited, Repr, DecidableEq

structure Substitution where
  a : List Nat
  b : List Nat
  c : List Nat
  deriving Inhabited, Repr, DecidableEq

structure Certificate where
  steps : Array LinearStep
  rules : Array Rule
  substitutions : Array Substitution
  «matches» : Array Match
  deriving Inhabited, Repr

def modulus : Nat := R1CS.scalarPrime

def insertSparse {Key : Type} [DecidableEq Key] (less : Key → Key → Bool)
    (key : Key) (coefficient : Nat) : List (Key × Nat) → List (Key × Nat)
  | [] => if coefficient % modulus = 0 then [] else [(key, coefficient % modulus)]
  | (other, value) :: rest =>
    if coefficient % modulus = 0 then (other, value) :: rest
    else if key = other then
      let total := (coefficient + value) % modulus
      if total = 0 then rest else (key, total) :: rest
    else if less key other then (key, coefficient % modulus) :: (other, value) :: rest
    else (other, value) :: insertSparse less key coefficient rest

def normalizeSparse {Key : Type} [DecidableEq Key] (less : Key → Key → Bool)
    (row : List (Key × Nat)) : List (Key × Nat) :=
  row.foldl (fun current term => insertSparse less term.1 term.2 current) []

def insertLinear (index coefficient : Nat) (row : Linear) : Linear :=
  insertSparse (fun first second : Nat => first < second) index coefficient row

def normalizeLinear (row : Linear) : Linear :=
  normalizeSparse (fun first second : Nat => first < second) row

def addLinear (left right : Linear) : Linear := normalizeLinear (left ++ right)

def scaleLinear (scale : Nat) (row : Linear) : Linear :=
  normalizeLinear (row.map fun (index, coefficient) => (index, scale * coefficient % modulus))

def coefficient (index : Nat) (row : Linear) : Nat :=
  (row.foldl (fun total term => if term.1 = index then total + term.2 else total) 0) % modulus

def orderedPair (first second : Nat) : Monomial :=
  if first ≤ second then (first, second) else (second, first)

def monomialLess (left right : Monomial) : Bool :=
  left.1 < right.1 || (left.1 == right.1 && left.2 < right.2)

def insertQuadratic (term : Monomial) (coefficient : Nat) (row : Quadratic) : Quadratic :=
  insertSparse monomialLess term coefficient row

def normalizeQuadratic (row : Quadratic) : Quadratic :=
  (normalizeSparse (fun _ _ => true)
    (row.mergeSort (fun first second =>
      decide (first.1 = second.1) || monomialLess first.1 second.1))).reverse

def scaleQuadratic (scale : Nat) (row : Quadratic) : Quadratic :=
  normalizeQuadratic (row.map fun (term, coefficient) => (term, scale * coefficient % modulus))

def equationPolynomial (equation : Equation) : Quadratic :=
  normalizeQuadratic <|
    (equation.a.flatMap fun (first, a) =>
      equation.b.map fun (second, b) => (orderedPair first second, a * b % modulus)) ++
    (equation.c.map fun (index, coefficient) =>
      ((0, index), (modulus - coefficient % modulus) % modulus))

def ofConstraint (row : R1CS.Constraint) : Equation :=
  ⟨row.a.terms.toList, row.b.terms.toList, row.c.terms.toList⟩

def maximumRows : Nat := 100000
def maximumSteps : Nat := 200000
def maximumWorkingWidth : Nat := 4096
def maximumPolynomialTerms : Nat := 131072
def maximumSubstitutionSteps : Nat := 2000000

def rowAdmitted (limit : Nat) (row : Linear) : Bool :=
  row.length ≤ maximumWorkingWidth && row.all (fun term => term.1 < limit && term.2 < modulus)

def equationAdmitted (limit : Nat) (row : Equation) : Bool :=
  rowAdmitted limit row.a && rowAdmitted limit row.b && rowAdmitted limit row.c

/-- The untrusted transcript selects algebraic operations; every row value
is computed from earlier rows. No claimed row contents are accepted. -/
def deriveStep (rows : Array Linear) (step : LinearStep) : Except String Linear := do
  match step with
  | .scale source scalar =>
    if source >= rows.size || scalar >= modulus then
      throw "Invalid constraint-certificate scale reference."
    pure (scaleLinear scalar rows[source]!)
  | .add left right =>
    if left >= rows.size || right >= rows.size then
      throw "Invalid constraint-certificate addition reference."
    pure (addLinear rows[left]! rows[right]!)

def deriveRows (initial : Array Linear) (steps : Array LinearStep) :
    Except String (Array Linear) := do
  let mut rows := initial.map normalizeLinear
  for step in steps do
    let next ← deriveStep rows step
    if next.length > maximumWorkingWidth then
      throw "Constraint-certificate working row is too wide."
    rows := rows.push next
  return rows

def checkRules (nVars nSignals : Nat) (rows : Array Linear) (rules : Array Rule) :
    Except String Unit := do
  for rule in rules do
    if rule.row >= rows.size || rule.pivot < nVars || rule.pivot >= nSignals then
      throw "Invalid constraint-certificate pivot reference."
    let row := rows[rule.row]!
    if coefficient rule.pivot row != 1 ||
        row.any (fun term => term.1 != rule.pivot && term.1 >= rule.pivot) then
      throw "Invalid constraint-certificate pivot row."

/-- A finite checked substitution program. Each subtracted row was derived
from source equations, so its choice cannot change an admitted assignment. -/
def substituteStep (rows : Array Linear) (rules : Array Rule) (row : Linear)
    (instruction : Nat) : Except String Linear := do
  if instruction >= rules.size then throw "Invalid constraint-certificate substitution reference."
  let rule := rules[instruction]!
  if rule.row >= rows.size then throw "Invalid constraint-certificate basis reference."
  let factor := (modulus - coefficient rule.pivot row) % modulus
  let next := addLinear row (scaleLinear factor rows[rule.row]!)
  if next.length > maximumWorkingWidth then
    throw "Constraint-certificate substituted row is too wide."
  return next

def substitute (rows : Array Linear) (rules : Array Rule) (initial : Linear)
    (program : List Nat) : Except String Linear := do
  let mut row := normalizeLinear initial
  for instruction in program do
    row ← substituteStep rows rules row instruction
  return row

def substituteEquation (nVars : Nat) (rows : Array Linear) (rules : Array Rule)
    (equation : Equation) (program : Substitution) : Except String Equation := do
  let a ← substitute rows rules equation.a program.a
  let b ← substitute rows rules equation.b program.b
  let c ← substitute rows rules equation.c program.c
  if !equationAdmitted nVars ⟨a, b, c⟩ then
    throw "Constraint-certificate auxiliary elimination is incomplete."
  if a.length * b.length + c.length > maximumPolynomialTerms then
    throw "Constraint-certificate polynomial is too large."
  return ⟨a, b, c⟩

def substituteAll (nVars : Nat) (rows : Array Linear) (rules : Array Rule)
    (nonlinear : Array Equation) (programs : Array Substitution) : Except String (Array Equation) := do
  let mut substituted := #[]
  for index in [0:nonlinear.size] do
    substituted := substituted.push (← substituteEquation nVars rows rules nonlinear[index]! programs[index]!)
  return substituted

def checkMatch (substituted : Array Equation) (target : Equation) (selected : Match) : Except String Unit := do
  if selected.source >= substituted.size || selected.scale == 0 || selected.scale >= modulus then
    throw "Constraint-certificate target reference is invalid."
  if target.a.length * target.b.length + target.c.length > maximumPolynomialTerms then
    throw "Constraint-certificate target polynomial is too large."
  if equationPolynomial target != scaleQuadratic selected.scale
      (equationPolynomial substituted[selected.source]!) then
    throw "Constraint-certificate polynomial correspondence failed."

def checkMatches (substituted targets : Array Equation) (selections : Array Match) : Except String Unit := do
  for index in [0:targets.size] do
    checkMatch substituted targets[index]! selections[index]!

/-- Validate an untrusted public certificate for every target row. Source
equations are supplied by the graph checker, never by a secret witness. -/
def dimensionsInvalid (nVars nSignals : Nat) (linears : Array Linear)
    (nonlinear targets : Array Equation) (certificate : Certificate) : Bool :=
  nVars == 0 || nVars > nSignals || nSignals > maximumRows ||
      linears.size > maximumRows || nonlinear.size > maximumRows || targets.size > maximumRows ||
      certificate.steps.size > maximumSteps || certificate.rules.size > maximumRows ||
      certificate.substitutions.size != nonlinear.size || certificate.matches.size != targets.size

def rowsInvalid (nVars nSignals : Nat) (linears : Array Linear) (nonlinear targets : Array Equation) : Bool :=
  !linears.all (rowAdmitted nSignals) || !nonlinear.all (equationAdmitted nSignals) ||
    !targets.all (equationAdmitted nVars)

def substitutionCount (certificate : Certificate) : Nat :=
  certificate.substitutions.foldl
    (fun count program => count + program.a.length + program.b.length + program.c.length) 0

def checkCertificate (nVars nSignals : Nat) (linears : Array Linear)
    (nonlinear targets : Array Equation) (certificate : Certificate) : Except String Unit := do
  if dimensionsInvalid nVars nSignals linears nonlinear targets certificate then
    throw "Constraint-certificate dimensions are invalid."
  if rowsInvalid nVars nSignals linears nonlinear targets then
    throw "Constraint-certificate source or target row is invalid."
  if substitutionCount certificate > maximumSubstitutionSteps then throw "Constraint-certificate substitution budget exceeded."
  let rows ← deriveRows linears certificate.steps
  checkRules nVars nSignals rows certificate.rules
  let substituted ← substituteAll nVars rows certificate.rules nonlinear certificate.substitutions
  checkMatches substituted targets certificate.matches

/-- Public-data gate indexed by the exact checked source, target, and
transcript. The only field is erased evidence; no assignment is stored. -/
structure CheckedCertificate (nVars nSignals : Nat) (linears : Array Linear)
    (nonlinear targets : Array Equation) (certificate : Certificate) : Type where
  private mk ::
  private accepted : checkCertificate nVars nSignals linears nonlinear targets certificate = .ok ()

def prepareCertificate (nVars nSignals : Nat) (linears : Array Linear)
    (nonlinear targets : Array Equation) (certificate : Certificate) :
    Except String (CheckedCertificate nVars nSignals linears nonlinear targets certificate) :=
  match checked : checkCertificate nVars nSignals linears nonlinear targets certificate with
  | .error failure => .error failure
  | .ok () => .ok ⟨checked⟩

theorem checkedCertificate_accepted (nVars nSignals : Nat) (linears : Array Linear)
    (nonlinear targets : Array Equation) (certificate : Certificate)
    (checked : CheckedCertificate nVars nSignals linears nonlinear targets certificate) :
    checkCertificate nVars nSignals linears nonlinear targets certificate = .ok () := checked.accepted

theorem prepareCertificate_success (nVars nSignals : Nat) (linears : Array Linear)
    (nonlinear targets : Array Equation) (certificate : Certificate)
    (checked : CheckedCertificate nVars nSignals linears nonlinear targets certificate)
    (_returned : prepareCertificate nVars nSignals linears nonlinear targets certificate = .ok checked) :
    checkCertificate nVars nSignals linears nonlinear targets certificate = .ok () :=
  checkedCertificate_accepted nVars nSignals linears nonlinear targets certificate checked


end LeanCrypto.Groth16.ConstraintCertificate

#print axioms LeanCrypto.Groth16.ConstraintCertificate.checkedCertificate_accepted
#print axioms LeanCrypto.Groth16.ConstraintCertificate.prepareCertificate_success
