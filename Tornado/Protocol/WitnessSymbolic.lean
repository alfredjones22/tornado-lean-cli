import Tornado.Protocol.WitnessVM
import Std.Data.HashMap

set_option autoImplicit false
namespace Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.Groth16R1CS

/-- Public field-expression DAG. References always point to earlier nodes;
inputs refer only to the original 49-slot prefix and supplied commitment. -/
inductive Node where
  | input (index : Nat)
  | constant (value : Nat)
  | bit (source position : Nat)
  | add (left right : Nat)
  | sub (left right : Nat)
  | mul (left right : Nat)
  | inverse (source : Nat)
  | select (selector left right : Nat)
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

def Node.references : Node → List Nat
  | .input _ | .constant _ => []
  | .bit source _ | .inverse source => [source]
  | .add left right | .sub left right | .mul left right => [left,right]
  | .select selector left right => [selector,left,right]

/-- Independent, total mathematical value. Inverse is the canonical Fermat
power; source admissibility separately requires nonzero inverse denominators. -/
def Node.meaning (inputs values : Array Nat) : Node → Nat
  | .input index => inputs[index]!
  | .constant value => value
  | .bit source position => bitValue values[source]! position
  | .add left right => (values[left]! + values[right]!) % scalarPrime
  | .sub left right => (values[left]! + scalarPrime - values[right]! % scalarPrime) % scalarPrime
  | .mul left right => values[left]! * values[right]! % scalarPrime
  | .inverse source => LeanCrypto.Groth16.FFT.powMod values[source]! (scalarPrime-2)
  | .select selector left right =>
    (dualMuxValues values[selector]! values[left]! values[right]!).1

def constantAt (nodes : Array Node) (index : Nat) : Option Nat :=
  match nodes[index]? with
  | some (.constant value) => some value
  | _ => none

/-- Public-only constant folding. No original source or witness value is read. -/
def foldConstant (nodes : Array Node) : Node → Option Nat
  | .input _ | .constant _ => none
  | .bit source position => do
    let value ← constantAt nodes source
    pure (bitValue value position)
  | .add left right => do
    let x ← constantAt nodes left
    let y ← constantAt nodes right
    pure ((x+y)%scalarPrime)
  | .sub left right => do
    let x ← constantAt nodes left
    let y ← constantAt nodes right
    pure ((x+scalarPrime-y%scalarPrime)%scalarPrime)
  | .mul left right => do
    let x ← constantAt nodes left
    let y ← constantAt nodes right
    pure (x*y%scalarPrime)
  | .inverse source => do
    let x ← constantAt nodes source
    pure (LeanCrypto.Groth16.FFT.powMod x (scalarPrime-2))
  | .select selector left right => do
    let s ← constantAt nodes selector
    let x ← constantAt nodes left
    let y ← constantAt nodes right
    pure ((dualMuxValues s x y).1)

/-- Validate every proposed result independently of the lookup implementation.
A malformed or substituted lookup can only cause a public validation error. -/
def checkOperation (nodes : Array Node) (operation : Node) (candidate : Nat) : Bool :=
  match nodes[candidate]? with
  | none => false
  | some actual => decide (actual = operation) ||
    match foldConstant nodes operation with
    | none => false
    | some value => decide (actual = .constant value)

def nodeValid (index : Nat) (node : Node) : Bool :=
  node.references.all (· < index) && match node with
    | .constant value => decide (value < scalarPrime)
    | .input source => decide (source < 50)
    | .bit _ position => decide (position < 248)
    | _ => true

def tableValid (nodes : Array Node) : Bool :=
  (List.range nodes.size).all fun index => nodeValid index nodes[index]!

structure Resolver where
  nodes : Array Node
  lookup : Std.HashMap Node Nat

def Resolver.ofNodes (nodes : Array Node) : Resolver := Id.run do
  let mut lookup := ∅
  for index in [0:nodes.size] do
    lookup := lookup.insert nodes[index]! index
  return ⟨nodes,lookup⟩

def operationKey (nodes : Array Node) (operation : Node) : Node :=
  match foldConstant nodes operation with
  | some value => .constant value
  | none => operation

def Resolver.resolve (resolver : Resolver) (operation : Node) : Except String Nat := do
  let key := operationKey resolver.nodes operation
  let candidate ← match resolver.lookup[key]? with
    | none => throw "Public witness DAG has no required expression."
    | some candidate => pure candidate
  if !checkOperation resolver.nodes operation candidate then
    throw "Public witness DAG expression does not match the required operation."
  return candidate

end Tornado.Protocol.WitnessSymbolic
