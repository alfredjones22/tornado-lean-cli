import Tornado.Protocol.WitnessGraphCertificate
import LeanCrypto.Groth16.ConstraintCertificate

set_option autoImplicit false
namespace Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.WitnessVM
open LeanCrypto.Groth16.ConstraintCertificate

abbrev negLinear (row : Linear) : Linear := scaleLinear (modulus-1) row
abbrev minusLinear (left right : Linear) : Linear := addLinear left (negLinear right)
def constantLinear (value : Nat) : Linear := normalizeLinear [(0,value)]
def atomLinear (index : Nat) : Linear := [(index,1)]

def signalLinear (nodes : Array Node) (compiled : CompiledGraph) (index : Nat) : Linear :=
  match constantAt nodes compiled.signalRoots[index]! with
  | some value => constantLinear value
  | none => atomLinear index

def asConstant : Linear → Option Nat
  | [] => some 0
  | [(0,value)] => some value
  | _ => none

structure LocalSystem where
  linears : Array Linear := #[]
  nonlinear : Array Equation := #[]

def LocalSystem.linear (system : LocalSystem) (row : Linear) : LocalSystem :=
  let row := normalizeLinear row
  if row.isEmpty then system else {system with linears := system.linears.push row}

def LocalSystem.equality (system : LocalSystem) (output : Nat) (expression : Linear) : LocalSystem :=
  system.linear (minusLinear (atomLinear output) expression)

def LocalSystem.constraint (system : LocalSystem) (a b c : Linear) : LocalSystem :=
  match asConstant a with
  | some value => system.linear (minusLinear (scaleLinear value b) c)
  | none => match asConstant b with
    | some value => system.linear (minusLinear (scaleLinear value a) c)
    | none => {system with nonlinear := system.nonlinear.push ⟨a,b,c⟩}

def LocalSystem.product (system : LocalSystem) (output : Nat) (a b : Linear) : LocalSystem :=
  system.constraint a b (atomLinear output)

def sumLinear (rows : List Linear) : Linear := rows.foldl addLinear []

def primitiveLocalSystem (nodes : Array Node) (compiled : CompiledGraph)
    (system : LocalSystem) (p : Tornado.Protocol.WitnessVM.Primitive) : Except String LocalSystem := do
  let row := signalLinear nodes compiled
  let input := p.inputs.map row
  let output := fun i => row p.outputs[i]!
  let x := input[0]?.getD []; let y := input[1]?.getD []
  let z := input[2]?.getD []; let w := input[3]?.getD []
  let mut accumulated := system
  for index in p.outputs do
    match constantAt nodes compiled.signalRoots[index]! with
    | none => pure ()
    | some value => accumulated := accumulated.equality index (constantLinear value)
  let system := accumulated
  match p.kind with
  | "Square" => return system.product p.outputs[0]! x x
  | "MontgomeryAdd" =>
    return ((system.constraint (output 0) (minusLinear z x) (minusLinear w y)).constraint
      (output 0) (output 0) (sumLinear [output 1,constantLinear 168698,x,z])).constraint
      (output 0) (minusLinear x (output 1)) (addLinear (output 2) y)
  | "MontgomeryDouble" =>
    return (((system.product p.outputs[0]! x x).constraint (output 1) (scaleLinear 2 y)
      (sumLinear [scaleLinear 3 (output 0),scaleLinear 337396 x,constantLinear 1])).constraint
      (output 1) (output 1) (sumLinear [output 2,constantLinear 168698,scaleLinear 2 x])).constraint
      (output 1) (minusLinear x (output 2)) (addLinear (output 3) y)
  | "Edwards2Montgomery" =>
    return (system.constraint (output 0) (minusLinear (constantLinear 1) y)
      (addLinear (constantLinear 1) y)).constraint (output 1) x (output 0)
  | "Montgomery2Edwards" =>
    return (system.constraint (output 0) y x).constraint (output 1)
      (addLinear x (constantLinear 1)) (minusLinear x (constantLinear 1))
  | "BabyAdd" =>
    return (((((system.product p.outputs[0]! x w).product p.outputs[1]! y z).constraint
      (minusLinear y (scaleLinear 168700 x)) (addLinear z w) (output 2)).product
      p.outputs[3]! (output 0) (output 1)).constraint (output 4)
      (addLinear (constantLinear 1) (scaleLinear 168696 (output 3))) (addLinear (output 0) (output 1))).constraint
      (output 5) (minusLinear (constantLinear 1) (scaleLinear 168696 (output 3)))
      (minusLinear (addLinear (output 2) (scaleLinear 168700 (output 0))) (output 1))
  | "Window4" =>
    return system.constraint (scaleLinear 2 x) y (minusLinear x (output 0))
  | "MultiMux3" =>
    let mut result := system.product p.outputs[0]! input[1]! input[0]!
    for coordinate in [0:2] do
      let c := fun i => input[3+coordinate*8+i]!
      let index := fun i => p.outputs[1+i*2+coordinate]!
      let out := fun i => row (index i)
      let a210 := sumLinear [c 7,negLinear (c 6),negLinear (c 5),c 4,
        negLinear (c 3),c 2,c 1,negLinear (c 0)]
      result := result.product (index 0) a210 (output 0)
      result := result.product (index 1) (sumLinear [c 6,negLinear (c 4),negLinear (c 2),c 0]) input[1]!
      result := result.product (index 2) (sumLinear [c 5,negLinear (c 4),negLinear (c 1),c 0]) input[0]!
      result := result.equality (index 3) (minusLinear (c 4) (c 0))
      result := result.product (index 4) (sumLinear [c 3,negLinear (c 2),negLinear (c 1),c 0]) (output 0)
      result := result.product (index 5) (minusLinear (c 2) (c 0)) input[1]!
      result := result.product (index 6) (minusLinear (c 1) (c 0)) input[0]!
      result := result.equality (index 7) (c 0)
      result := result.constraint (sumLinear [out 0,out 1,out 2,out 3]) input[2]!
        (minusLinear (out 8) (sumLinear [out 4,out 5,out 6,c 0]))
    return result
  | _ => throw "Public witness local constraint kind is unsupported."

def feistelLocalSystem (nodes : Array Node) (compiled : CompiledGraph)
    (constants : Array Nat) (system : LocalSystem) (f : Feistel) : LocalSystem := Id.run do
  let row := signalLinear nodes compiled
  let mut left := row f.leftInput
  let mut right := row f.rightInput
  let mut result := system
  for round in [0:220] do
    let t := sumLinear [left,row f.key,constantLinear constants[round]!]
    result := result.product f.t2[round]! t t
    result := result.product f.t4[round]! (row f.t2[round]!) (row f.t2[round]!)
    if round < 219 then
      result := result.constraint (row f.t4[round]!) t (minusLinear (row f.leftRounds[round]!) right)
      result := result.equality f.rightRounds[round]! left
      left := row f.leftRounds[round]!
      right := row f.rightRounds[round]!
    else
      result := result.equality f.leftOutput left
      result := result.constraint (row f.t4[round]!) t (minusLinear (row f.rightOutput) right)
  return result

def merkleLocalSystem (nodes : Array Node) (compiled : CompiledGraph) (constants : Array Nat)
    (system : LocalSystem) (level : MerkleLevel) (sponge : SpongeLevel) : LocalSystem := Id.run do
  let row := signalLinear nodes compiled
  let mut result := system.constraint (minusLinear (row level.rightInput) (row level.leftInput))
    (row level.selector) (minusLinear (row level.leftOutput) (row level.leftInput))
  result := result.constraint (minusLinear (row level.leftInput) (row level.rightInput))
    (row level.selector) (minusLinear (row level.rightOutput) (row level.rightInput))
  result := result.constraint (row level.selector) (minusLinear (row level.selector) (constantLinear 1)) []
  result := result.equality sponge.first.key (constantLinear 0)
  result := result.equality sponge.first.leftInput (row level.leftOutput)
  result := result.equality sponge.first.rightInput (constantLinear 0)
  result := feistelLocalSystem nodes compiled constants result sponge.first
  result := result.equality sponge.second.key (constantLinear 0)
  result := result.equality sponge.second.leftInput
    (addLinear (row sponge.first.leftOutput) (row level.rightOutput))
  result := result.equality sponge.second.rightInput (row sponge.first.rightOutput)
  result := feistelLocalSystem nodes compiled constants result sponge.second
  result := result.equality level.hashOutput (row sponge.second.leftOutput)
  return result

/-- Generate local equations from actual decoded public metadata and validated
expression roots. Neither this function nor its elimination checker receives a
secret input, generated assignment, or final R1CS-check result. -/
def generateLocalSystemWith (nodes : Array Node) (compiled : CompiledGraph)
    (graph : SelectedGraph) (constants : Array Nat) : Except String LocalSystem := do
  if !graph.layoutValid || compiled.signalRoots.size != graph.nSignals || constants.size != 220 then
    throw "Public witness local system has an invalid shape."
  let row := signalLinear nodes compiled
  let mut result : LocalSystem := {}
  for component in graph.num2bits do
    let mut reconstructed : Linear := []
    for bit in [0:component.outputs.size] do
      let output := row component.outputs[bit]!
      result := result.constraint output (minusLinear output (constantLinear 1)) []
      reconstructed := addLinear reconstructed (scaleLinear (2^bit) output)
    result := result.linear (minusLinear (row component.input) reconstructed)
  for base in graph.bases do result := result.equality base.index (constantLinear base.value)
  for primitive in graph.primitives do
    result ← primitiveLocalSystem nodes compiled result primitive
  result := result.linear (minusLinear (row 28300) (row 2))
  for i in [0:20] do
    result := merkleLocalSystem nodes compiled constants result graph.merkle[i]! graph.feistel[i]!
  result := result.linear (minusLinear (row graph.rootSignal) (row graph.merkle[19]!.hashOutput))
  return result

def generateLocalSystem (nodes : Array Node) (compiled : CompiledGraph)
    (graph : SelectedGraph) : Except String LocalSystem :=
  generateLocalSystemWith nodes compiled graph Tornado.Crypto.mimcConstants

end Tornado.Protocol.WitnessSymbolic
