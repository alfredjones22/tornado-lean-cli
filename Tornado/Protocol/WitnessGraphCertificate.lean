import Tornado.Protocol.WitnessExpressions

set_option autoImplicit false
namespace Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.Groth16R1CS

structure SignalState where
  slots : Array (Option Nat)
  commitmentAliases : Array (Nat × Nat) := #[]

def SignalState.empty (size : Nat) : SignalState := ⟨Array.replicate size none,#[]⟩

def SignalState.read (state : SignalState) (index : Nat) : Except String Nat := do
  if index >= state.slots.size then throw "Public witness DAG signal index is out of bounds."
  match state.slots[index]! with
  | none => throw "Public witness DAG reads a signal before assignment."
  | some node => pure node

def SignalState.write (state : SignalState) (index node : Nat) : Except String SignalState := do
  if index >= state.slots.size then throw "Public witness DAG output index is out of bounds."
  match state.slots[index]! with
  | none => pure {state with slots := state.slots.set! index (some node)}
  | some prior =>
    if prior == node then pure state
    else if index == 49 then
      pure {state with commitmentAliases := state.commitmentAliases.push (prior,node)}
    else throw "Public witness DAG contains inconsistent signal aliases."

def SignalState.writeMany (state : SignalState) (indices values : Array Nat) :
    Except String SignalState := do
  if indices.size != values.size then throw "Public witness DAG output count differs from metadata."
  let mut result := state
  for i in [0:values.size] do result ← result.write indices[i]! values[i]!
  pure result

def compileNum2Bits (resolver : Resolver) (state : SignalState)
    (component : Num2BitsComponent) : Except String SignalState := do
  if component.outputs.size != 248 then throw "Public witness DAG bit width differs from 248."
  let input ← state.read component.input
  let mut result := state
  for i in [0:component.outputs.size] do
    let node ← resolver.resolve (.bit input i)
    result ← result.write component.outputs[i]! node
  pure result

def compilePrimitiveStage (resolver : Resolver) (state : SignalState)
    (primitive : Tornado.Protocol.WitnessVM.Primitive) : Except String SignalState := do
  if !primitive.shapeValid state.slots.size then throw "Public witness DAG primitive is malformed."
  let inputs ← primitive.inputs.mapM state.read
  let outputs ← compilePrimitive resolver primitive.kind inputs
  state.writeMany primitive.outputs outputs

def compileFeistelRound (resolver : Resolver) (constants : Array Nat) (stage : Feistel)
    (key round : Nat) (frame : FeistelFrame SignalState) : Except String (FeistelFrame SignalState) := do
  let constant ← resolver.resolve (.constant constants[round]!)
  let keyed ← resolver.resolve (.add frame.left key)
  let t ← resolver.resolve (.add keyed constant)
  let square ← resolver.resolve (.mul t t)
  let fourth ← resolver.resolve (.mul square square)
  let fifth ← resolver.resolve (.mul fourth t)
  let first ← frame.state.write stage.t2[round]! square
  let second ← first.write stage.t4[round]! fourth
  let next ← resolver.resolve (.add frame.right fifth)
  if round < 219 then
    let third ← second.write stage.leftRounds[round]! next
    let fourthState ← third.write stage.rightRounds[round]! frame.left
    return ⟨fourthState, next, frame.left⟩
  else
    let third ← second.write stage.leftOutput frame.left
    let fourthState ← third.write stage.rightOutput next
    return ⟨fourthState, frame.left, next⟩

def compileFeistel (resolver : Resolver) (constants : Array Nat) (state : SignalState)
    (stage : Feistel) : Except String SignalState := do
  if constants.size != 220 || !stage.layoutValid state.slots.size then
    throw "Public witness DAG Feistel layout or constants are invalid."
  let key ← state.read stage.key
  let left ← state.read stage.leftInput
  let right ← state.read stage.rightInput
  let mut frame : FeistelFrame SignalState := ⟨state, left, right⟩
  for round in [0:220] do
    frame ← compileFeistelRound resolver constants stage key round frame
  pure frame.state

def compileDualMux (resolver : Resolver) (state : SignalState) (level : MerkleLevel) :
    Except String (SignalState × Nat × Nat) := do
  let leftInput ← state.read level.leftInput
  let rightInput ← state.read level.rightInput
  let selector ← state.read level.selector
  let left ← resolver.resolve (.select selector leftInput rightInput)
  let right ← resolver.resolve (.select selector rightInput leftInput)
  let withLeft ← state.write level.leftOutput left
  let withRight ← withLeft.write level.rightOutput right
  pure (withRight,left,right)

def compileMerkleLevel (resolver : Resolver) (constants : Array Nat) (state : SignalState)
    (level : MerkleLevel) (sponge : SpongeLevel) : Except String SignalState := do
  let (withRight,left,right) ← compileDualMux resolver state level
  let zeroNode ← resolver.resolve (.constant 0)
  let mut firstInputs := withRight
  firstInputs ← firstInputs.write sponge.first.key zeroNode
  firstInputs ← firstInputs.write sponge.first.leftInput left
  firstInputs ← firstInputs.write sponge.first.rightInput zeroNode
  let first ← compileFeistel resolver constants firstInputs sponge.first
  let intermediateLeft ← first.read sponge.first.leftOutput
  let intermediateRight ← first.read sponge.first.rightOutput
  let mut secondInputs := first
  secondInputs ← secondInputs.write sponge.second.key zeroNode
  let absorbed ← resolver.resolve (.add intermediateLeft right)
  secondInputs ← secondInputs.write sponge.second.leftInput absorbed
  secondInputs ← secondInputs.write sponge.second.rightInput intermediateRight
  let second ← compileFeistel resolver constants secondInputs sponge.second
  let hash ← second.read sponge.second.leftOutput
  second.write level.hashOutput hash

structure CompiledGraph where
  signalRoots : Array Nat
  commitmentAliases : Array (Nat × Nat)
  publicRoot : Nat × Nat
  publicNullifier : Nat × Nat

def compileGraphWith (resolver : Resolver) (graph : SelectedGraph) (constants : Array Nat) :
    Except String CompiledGraph := do
  if !graph.layoutValid || !tableValid resolver.nodes then
    throw "Public witness DAG or selected graph has invalid structure."
  let mut state := SignalState.empty graph.nSignals
  for i in [0:49] do
    let node ← if i == 0 then resolver.resolve (.constant 1)
      else resolver.resolve (.input i)
    state ← state.write i node
  let commitment ← resolver.resolve (.input 49)
  state ← state.write graph.commitmentSignal commitment
  for component in graph.num2bits do state ← compileNum2Bits resolver state component
  for base in graph.bases do
    let value ← resolver.resolve (.constant base.value)
    state ← state.write base.index value
  for primitive in graph.primitives do state ← compilePrimitiveStage resolver state primitive
  for i in [0:20] do
    state ← compileMerkleLevel resolver constants state graph.merkle[i]! graph.feistel[i]!
  let publicRoot ← state.read graph.rootSignal
  let computedRoot ← state.read graph.merkle[19]!.hashOutput
  let publicNullifier ← state.read 2
  let computedNullifier ← state.read 28300
  let signalRoots ← state.slots.mapM fun slot => match slot with
    | none => throw "Public witness DAG does not assign every internal signal."
    | some value => pure value
  pure ⟨signalRoots,state.commitmentAliases,(publicRoot,computedRoot),
    (publicNullifier,computedNullifier)⟩

def compileGraph (resolver : Resolver) (graph : SelectedGraph) : Except String CompiledGraph :=
  compileGraphWith resolver graph Tornado.Crypto.mimcConstants

end Tornado.Protocol.WitnessSymbolic
