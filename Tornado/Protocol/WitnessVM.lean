import Lean
import LeanCrypto.Groth16.FFT
import Tornado.Crypto.MiMCTree
import Tornado.Crypto.SHA256
import Tornado.Protocol.TornadoWitness

/-!
Native signal evaluator for the pinned Tornado Withdraw(20) Circom program.
The authenticated graph supplies signal aliases and a topologically ordered
program of point, mux, square, bit, and MiMC operations. Evaluation assigns
all 36,528 signals in the supported circuit and can return a complete witness
only after every R1CS variable is present and all 28,275 constraints pass.

Signal slots remain optional until computed. A missing or conflicting signal
fails closed. The graph and supplied R1CS circuit must be authenticated at the
caller boundary; satisfying the R1CS does not construct a Groth16 proof.
-/

namespace Tornado.Protocol.WitnessVM

open Lean Tornado.Crypto Tornado.Protocol.Groth16R1CS

structure Num2BitsComponent where
  name : String
  input : Nat
  outputs : Array Nat
  deriving Inhabited, Repr

structure MerkleLevel where
  level : Nat
  leftInput : Nat
  rightInput : Nat
  selector : Nat
  leftOutput : Nat
  rightOutput : Nat
  hashOutput : Nat
  deriving Inhabited, Repr

structure Feistel where
  key : Nat
  leftInput : Nat
  rightInput : Nat
  leftOutput : Nat
  rightOutput : Nat
  t2 : Array Nat
  t4 : Array Nat
  leftRounds : Array Nat
  rightRounds : Array Nat
  deriving Inhabited, Repr

structure SpongeLevel where
  first : Feistel
  second : Feistel
  deriving Inhabited, Repr

structure BaseSeed where
  index : Nat
  value : Nat
  deriving Inhabited, Repr

structure Primitive where
  kind : String
  name : String
  inputs : Array Nat
  outputs : Array Nat
  deriving Inhabited, Repr

structure SelectedGraph where
  nSignals : Nat
  nVars : Nat
  commitmentSignal : Nat
  rootSignal : Nat
  num2bits : Array Num2BitsComponent
  merkle : Array MerkleLevel
  feistel : Array SpongeLevel
  bases : Array BaseSeed
  primitives : Array Primitive
  deriving Inhabited, Repr

structure Assignment where
  values : Array (Option Nat)
  deriving Inhabited

def Assignment.empty (size : Nat) : Assignment :=
  ⟨Array.replicate size none⟩

def Assignment.read (state : Assignment) (index : Nat) : Except String Nat := do
  if index >= state.values.size then throw s!"Signal {index} is outside the pinned graph."
  match state.values[index]! with
  | none => throw s!"Signal {index} has not been computed."
  | some value => return value

/-- A signal may be assigned once, or reassigned only to the same value.
    This preserves Circom's alias consistency and rejects clashing paths. -/
def Assignment.write (state : Assignment) (index value : Nat) : Except String Assignment := do
  if index >= state.values.size then throw s!"Signal {index} is outside the pinned graph."
  if value >= scalarPrime then throw s!"Signal {index} is outside BN254 Fr."
  match state.values[index]! with
  | none => return ⟨state.values.set! index (some value)⟩
  | some prior =>
      if prior != value then throw s!"Signal {index} has inconsistent assignments."
      return state

private def field (json : Json) (name : String) : Except String Nat :=
  json.getObjVal? name >>= Json.getNat?

private def parseNum2Bits (json : Json) : Except String Num2BitsComponent := do
  let name ← (← json.getObjVal? "name").getStr?
  let input ← field json "input"
  let raw ← (← json.getObjVal? "outputs").getArr?
  let mut outputs := #[]
  for value in raw do outputs := outputs.push (← value.getNat?)
  return ⟨name, input, outputs⟩

private def parseMerkleLevel (json : Json) : Except String MerkleLevel := do
  return ⟨(← field json "level"), (← field json "leftInput"),
    (← field json "rightInput"), (← field json "selector"),
    (← field json "leftOutput"), (← field json "rightOutput"),
    (← field json "hashOutput")⟩

private def parseIndices (json : Json) (name : String) : Except String (Array Nat) := do
  let raw ← (← json.getObjVal? name).getArr?
  let mut values := #[]
  for item in raw do values := values.push (← item.getNat?)
  return values

private def parseFeistel (json : Json) : Except String Feistel := do
  return ⟨(← field json "key"), (← field json "leftInput"),
    (← field json "rightInput"), (← field json "leftOutput"),
    (← field json "rightOutput"), (← parseIndices json "t2"),
    (← parseIndices json "t4"), (← parseIndices json "leftRounds"),
    (← parseIndices json "rightRounds")⟩

private def parseSponge (json : Json) : Except String SpongeLevel := do
  let stages ← json.getArr?
  if stages.size != 2 then throw "MiMC sponge must have two Feistel stages."
  return ⟨(← parseFeistel stages[0]!), (← parseFeistel stages[1]!)⟩

private def parseBase (json : Json) : Except String BaseSeed := do
  let raw ← (← json.getObjVal? "value").getStr?
  if raw.isEmpty || !raw.toList.all Char.isDigit then
    throw "Pedersen base coordinate is not an unsigned decimal integer."
  let some value := raw.toNat?
    | throw "Pedersen base coordinate is malformed."
  if value >= scalarPrime then throw "Pedersen base coordinate exceeds BN254 Fr."
  return ⟨(← field json "index"), value⟩

private def parsePrimitive (json : Json) : Except String Primitive := do
  return ⟨(← (← json.getObjVal? "kind").getStr?),
    (← (← json.getObjVal? "name").getStr?),
    (← parseIndices json "inputs"), (← parseIndices json "outputs")⟩

def Primitive.shapeValid (primitive : Primitive) (nSignals : Nat) : Bool :=
  let dimensions := match primitive.kind with
    | "MontgomeryAdd" => (4, 3)
    | "MontgomeryDouble" => (2, 4)
    | "Edwards2Montgomery" | "Montgomery2Edwards" => (2, 2)
    | "BabyAdd" => (4, 6)
    | "Window4" => (2, 1)
    | "MultiMux3" => (19, 19)
    | "Square" => (1, 1)
    | _ => (0, 0)
  dimensions.1 > 0 && primitive.inputs.size == dimensions.1 &&
  primitive.outputs.size == dimensions.2 &&
  primitive.inputs.all (· < nSignals) &&
  primitive.outputs.all (· < nSignals)

def Feistel.layoutValid (feistel : Feistel) (nSignals : Nat) : Bool :=
  #[feistel.key, feistel.leftInput, feistel.rightInput,
      feistel.leftOutput, feistel.rightOutput].all (· < nSignals) &&
  feistel.t2.size == 220 && feistel.t4.size == 220 &&
  feistel.leftRounds.size == 219 && feistel.rightRounds.size == 219 &&
  feistel.t2.all (· < nSignals) && feistel.t4.all (· < nSignals) &&
  feistel.leftRounds.all (· < nSignals) &&
  feistel.rightRounds.all (· < nSignals)

/-- Check the exact 49-slot wiring on which this evaluator relies.
    The development extractor separately binds these indices to the hash-pinned
    original circuit JSON. -/
def SelectedGraph.layoutValid (graph : SelectedGraph) : Bool := Id.run do
  if graph.nSignals != 36528 || graph.nVars != 28300 ||
      graph.commitmentSignal != 49 || graph.rootSignal != 1 ||
      graph.num2bits.size != 2 || graph.merkle.size != 20 ||
      graph.feistel.size != 20 || graph.bases.size != 10 ||
      graph.primitives.size != 2234 then return false
  for i in [0:2] do
    let component := graph.num2bits[i]!
    if component.name !=
        (if i == 0 then "main.hasher.nullifierBits" else "main.hasher.secretBits") ||
        component.input != 7 + i || component.outputs.size != 248 ||
        component.outputs.any (· >= graph.nSignals) then return false
  for i in [0:20] do
    let level := graph.merkle[i]!
    let previous := if i == 0 then graph.commitmentSignal
      else graph.merkle[i - 1]!.hashOutput
    if level.level != i || level.leftInput != previous ||
        level.rightInput != 9 + i || level.selector != 29 + i ||
        level.leftOutput >= graph.nSignals ||
        level.rightOutput >= graph.nSignals ||
        level.hashOutput >= graph.nSignals then return false
    let sponge := graph.feistel[i]!
    if !sponge.first.layoutValid graph.nSignals ||
        !sponge.second.layoutValid graph.nSignals ||
        sponge.first.key != sponge.second.key ||
        sponge.first.leftInput != level.leftOutput ||
        sponge.second.rightInput != sponge.first.rightOutput ||
        sponge.second.leftOutput != level.hashOutput then return false
  if graph.bases.any (fun base =>
      base.index >= graph.nSignals || base.value >= scalarPrime) ||
      graph.primitives.any (fun item => !item.shapeValid graph.nSignals) then
    return false
  return true

def decodeSelectedGraph (json : Json) : Except String SelectedGraph := do
  let version ← field json "schemaVersion"
  let source ← (← json.getObjVal? "sourceCircuitSha256").getStr?
  if version != 1 || source !=
      "3ddd61dbff09caeec82d8edde95c674a3c34f9e66b1fe9f2c8783e72fe536f98" then
    throw "Selected component graph is not pinned to this Tornado circuit."
  let rawBits ← (← json.getObjVal? "num2bits").getArr?
  let rawMerkle ← (← json.getObjVal? "merkle").getArr?
  let rawFeistel ← (← json.getObjVal? "feistel").getArr?
  let rawBases ← (← json.getObjVal? "bases").getArr?
  let rawPrimitives ← (← json.getObjVal? "primitives").getArr?
  let mut num2bits := #[]
  let mut merkle := #[]
  let mut feistel := #[]
  let mut bases := #[]
  let mut primitives := #[]
  for item in rawBits do num2bits := num2bits.push (← parseNum2Bits item)
  for item in rawMerkle do merkle := merkle.push (← parseMerkleLevel item)
  for item in rawFeistel do feistel := feistel.push (← parseSponge item)
  for item in rawBases do bases := bases.push (← parseBase item)
  for item in rawPrimitives do primitives := primitives.push (← parsePrimitive item)
  let graph : SelectedGraph :=
    ⟨(← field json "nSignals"), (← field json "nVars"),
      (← field json "commitmentSignal"), (← field json "rootSignal"),
      num2bits, merkle, feistel, bases, primitives⟩
  if !graph.layoutValid then throw "Selected component graph wiring is invalid."
  return graph

def pinnedGraphSHA256 : String :=
  "0ac046333a730a9d7afe017d75debfe23ffcd2ce8f64931c59080ee3d44dec94"

/-- The private constructor and provenance proof tie the graph used by the
    final witness API to exact SHA-256-pinned, successfully decoded bytes. -/
structure PinnedGraph where
  private mk ::
  graph : SelectedGraph
  provenance : ∃ raw : String,
    sha256Hex raw.toUTF8 = pinnedGraphSHA256 ∧
    (Json.parse raw >>= decodeSelectedGraph) = .ok graph

/-- Pin the complete 1.2 MB arithmetic graph, not merely its advertised
    `sourceCircuitSha256` field. The development extractor independently
    regenerates these bytes from the hash-pinned original circuit. -/
def decodePinnedGraph (raw : String) : Except String PinnedGraph :=
  if digest : sha256Hex raw.toUTF8 = pinnedGraphSHA256 then
    match parsed : (Json.parse raw >>= decodeSelectedGraph) with
    | .error error => .error error
    | .ok graph => .ok ⟨graph, ⟨raw, digest, parsed⟩⟩
  else .error "Witness arithmetic graph differs from the pinned circuit extraction."

/-- Little-endian bit extraction used by the pinned Circom Num2Bits template. -/
def bitValue (value bit : Nat) : Nat := value / 2 ^ bit % 2

theorem bitValue_is_binary (value bit : Nat) : bitValue value bit < 2 := by
  exact Nat.mod_lt _ (by decide)

/-- DualMux chooses the two inputs in path-index order. -/
def dualMuxValues (selector input0 input1 : Nat) : Nat × Nat :=
  if selector == 0 then (input0, input1) else (input1, input0)

theorem dualMux_zero (input0 input1 : Nat) :
    dualMuxValues 0 input0 input1 = (input0, input1) := by
  simp [dualMuxValues]

theorem dualMux_one (input0 input1 : Nat) :
    dualMuxValues 1 input0 input1 = (input1, input0) := by
  simp [dualMuxValues]

private def fadd (x y : Nat) : Nat := (x + y) % scalarPrime
private def fsub (x y : Nat) : Nat := (x + scalarPrime - y % scalarPrime) % scalarPrime
private def fmul (x y : Nat) : Nat := x * y % scalarPrime

/-- Share the canonical total scalar-field exponentiation. The field modulus
is definitionally the same as the circuit field; the loop strictly halves the
exponent rather than hiding its equations behind an opaque while primitive. -/
private def powMod (base exponent : Nat) : Nat :=
  LeanCrypto.Groth16.FFT.powMod base exponent

/-- Inversion verifies its own equation. No primality assumption is needed to
    trust a returned inverse; a zero or nonunit denominator fails closed. -/
private def finv (x : Nat) : Except String Nat := do
  if x % scalarPrime == 0 then throw "Circuit point operation divides by zero."
  let candidate := powMod x (scalarPrime - 2)
  if fmul x candidate != 1 then throw "Circuit point denominator is not invertible."
  return candidate

private def muxCoordinate (inputs : Array Nat) (coordinate : Nat)
    (s0 s1 s2 s10 : Nat) : Array Nat := Id.run do
  let start := 3 + coordinate * 8
  let c0 := inputs[start]!
  let c1 := inputs[start + 1]!
  let c2 := inputs[start + 2]!
  let c3 := inputs[start + 3]!
  let c4 := inputs[start + 4]!
  let c5 := inputs[start + 5]!
  let c6 := inputs[start + 6]!
  let c7 := inputs[start + 7]!
  let a210 := fmul (fsub (fadd (fadd
    (fsub (fadd (fsub (fsub c7 c6) c5) c4) c3) c2) c1) c0) s10
  let a21 := fmul (fadd (fsub (fsub c6 c4) c2) c0) s1
  let a20 := fmul (fadd (fsub (fsub c5 c4) c1) c0) s0
  let a2 := fsub c4 c0
  let a10 := fmul (fadd (fsub (fsub c3 c2) c1) c0) s10
  let a1 := fmul (fsub c2 c0) s1
  let a0 := fmul (fsub c1 c0) s0
  let out := fadd (fmul (fadd (fadd (fadd a210 a21) a20) a2) s2)
    (fadd (fadd (fadd a10 a1) a0) c0)
  return #[a210, a21, a20, a2, a10, a1, a0, c0, out]

/-- Pure arithmetic output stage shared with constructive witness proofs.
Input/output wiring and write consistency remain checked by the caller. -/
def primitiveValues (kind : String) (inputs : Array Nat) : Except String (Array Nat) := do
  match kind with
      | "MontgomeryAdd" => do
          let x1 := inputs[0]!
          let y1 := inputs[1]!
          let x2 := inputs[2]!
          let y2 := inputs[3]!
          let lambda := fmul (fsub y2 y1) (← finv (fsub x2 x1))
          let outX := fsub (fsub (fsub (fmul lambda lambda) 168698) x1) x2
          let outY := fsub (fmul lambda (fsub x1 outX)) y1
          pure #[lambda, outX, outY]
      | "MontgomeryDouble" => do
          let x := inputs[0]!
          let y := inputs[1]!
          let xSquared := fmul x x
          let numerator := fadd (fadd (fmul 3 xSquared) (fmul (2 * 168698) x)) 1
          let lambda := fmul numerator (← finv (fmul 2 y))
          let outX := fsub (fsub (fmul lambda lambda) 168698) (fmul 2 x)
          let outY := fsub (fmul lambda (fsub x outX)) y
          pure #[xSquared, lambda, outX, outY]
      | "Edwards2Montgomery" => do
          let x := inputs[0]!
          let y := inputs[1]!
          let outX := fmul (fadd 1 y) (← finv (fsub 1 y))
          let outY := fmul outX (← finv x)
          pure #[outX, outY]
      | "Montgomery2Edwards" => do
          let x := inputs[0]!
          let y := inputs[1]!
          let outX := fmul x (← finv y)
          let outY := fmul (fsub x 1) (← finv (fadd x 1))
          pure #[outX, outY]
      | "BabyAdd" => do
          let x1 := inputs[0]!
          let y1 := inputs[1]!
          let x2 := inputs[2]!
          let y2 := inputs[3]!
          let beta := fmul x1 y2
          let gamma := fmul y1 x2
          let delta := fmul (fsub y1 (fmul 168700 x1)) (fadd x2 y2)
          let tau := fmul beta gamma
          let outX := fmul (fadd beta gamma)
            (← finv (fadd 1 (fmul 168696 tau)))
          let outY := fmul (fsub (fadd delta (fmul 168700 beta)) gamma)
            (← finv (fsub 1 (fmul 168696 tau)))
          pure #[beta, gamma, delta, tau, outX, outY]
      | "Window4" => do
          let muxY := inputs[0]!
          let sign := inputs[1]!
          if sign > 1 then throw "Window4 sign input is not a bit."
          pure #[fsub muxY (fmul (fmul 2 muxY) sign)]
      | "MultiMux3" => do
          let s0 := inputs[0]!
          let s1 := inputs[1]!
          let s2 := inputs[2]!
          if s0 > 1 || s1 > 1 || s2 > 1 then
            throw "MultiMux3 selector is not a bit."
          let s10 := fmul s1 s0
          let coordinate0 := muxCoordinate inputs 0 s0 s1 s2 s10
          let coordinate1 := muxCoordinate inputs 1 s0 s1 s2 s10
          let mut values := #[s10]
          for i in [0:9] do
            values := values.push coordinate0[i]!
            values := values.push coordinate1[i]!
          pure values
      | "Square" => pure #[fmul inputs[0]! inputs[0]!]
      | _ => throw s!"Unsupported circuit primitive {kind}."

/-- Evaluate one topologically ordered, typed Circom primitive over BN254 Fr.
    Every input must already have a native assignment; missing inputs fail
    rather than silently defaulting to the SDK fixture's value. -/
def evaluatePrimitive (state : Assignment) (primitive : Primitive) :
    Except String Assignment := do
  if !primitive.shapeValid state.values.size then
    throw s!"Unsupported or malformed circuit primitive {primitive.name}."
  let mut inputs := #[]
  for index in primitive.inputs do inputs := inputs.push (← state.read index)
  let outputs ← primitiveValues primitive.kind inputs
  if outputs.size != primitive.outputs.size then
    throw s!"Circuit primitive {primitive.name} output count differs from metadata."
  let mut result := state
  for i in [0:outputs.size] do
    result ← result.write primitive.outputs[i]! outputs[i]!
  return result

def executeNum2Bits (state : Assignment) (component : Num2BitsComponent) :
    Except String Assignment := do
  let input ← state.read component.input
  if component.outputs.size != 248 || input >= 2 ^ component.outputs.size then
    throw "Num2Bits(248) input cannot be reconstructed without field wraparound."
  let mut result := state
  for bit in [0:component.outputs.size] do
    result ← result.write component.outputs[bit]! (bitValue input bit)
  return result

/-- Explicit round frame for constructive Feistel execution. -/
structure FeistelFrame (State : Type) where
  state : State
  left : Nat
  right : Nat

def executeFeistelRound (constants : Array Nat) (stage : Feistel) (key round : Nat)
    (frame : FeistelFrame Assignment) : Except String (FeistelFrame Assignment) := do
  let t := (frame.left + key + constants[round]!) % scalarPrime
  let square := t * t % scalarPrime
  let fourth := square * square % scalarPrime
  let fifth := fourth * t % scalarPrime
  let first ← frame.state.write stage.t2[round]! square
  let second ← first.write stage.t4[round]! fourth
  let next := (frame.right + fifth) % scalarPrime
  if round < 219 then
    let third ← second.write stage.leftRounds[round]! next
    let fourthState ← third.write stage.rightRounds[round]! frame.left
    return ⟨fourthState, next, frame.left⟩
  else
    let third ← second.write stage.leftOutput frame.left
    let fourthState ← third.write stage.rightOutput next
    return ⟨fourthState, frame.left, next⟩

def executeFeistel (constants : Array Nat) (state : Assignment)
    (stage : Feistel) : Except String Assignment := do
  if constants.size != 220 || !stage.layoutValid state.values.size then
    throw "MiMCFeistel round constants or signal layout are invalid."
  let key ← state.read stage.key
  let left ← state.read stage.leftInput
  let right ← state.read stage.rightInput
  let mut frame : FeistelFrame Assignment := ⟨state, left, right⟩
  for round in [0:220] do
    frame ← executeFeistelRound constants stage key round frame
  return frame.state

/-- Execute the exact Circom DualMux read/bit-check/two-write stage. -/
def executeDualMux (state : Assignment) (level : MerkleLevel) :
    Except String (Assignment × Nat × Nat) := do
  let leftInput ← state.read level.leftInput
  let rightInput ← state.read level.rightInput
  let selector ← state.read level.selector
  if selector > 1 then throw "Merkle selector is not a bit."
  let (left, right) := dualMuxValues selector leftInput rightInput
  let withLeft ← state.write level.leftOutput left
  let withRight ← withLeft.write level.rightOutput right
  return (withRight, left, right)

def executeMerkleLevel (constants : Array Nat) (state : Assignment)
    (level : MerkleLevel) (sponge : SpongeLevel) :
    Except String Assignment := do
  let (withRight, left, right) ← executeDualMux state level
  let mut firstInputs := withRight
  firstInputs ← firstInputs.write sponge.first.key 0
  firstInputs ← firstInputs.write sponge.first.leftInput left
  firstInputs ← firstInputs.write sponge.first.rightInput 0
  let first ← executeFeistel constants firstInputs sponge.first
  let intermediateLeft ← first.read sponge.first.leftOutput
  let intermediateRight ← first.read sponge.first.rightOutput
  let mut secondInputs := first
  secondInputs ← secondInputs.write sponge.second.key 0
  secondInputs ← secondInputs.write sponge.second.leftInput
    ((intermediateLeft + right) % scalarPrime)
  secondInputs ← secondInputs.write sponge.second.rightInput intermediateRight
  let second ← executeFeistel constants secondInputs sponge.second
  let hash ← second.read sponge.second.leftOutput
  let independentHash ← mimcHashPairWith constants left right
  if hash != independentHash then
    throw "Computed MiMC round signals disagree with the native sponge."
  second.write level.hashOutput hash

/-- Evaluate the pinned graph from a checked 49-slot native input prefix and
    its recomputed note commitment. Unassigned slots remain `none`; callers
    must use `toWitness` and `finishCheckedWitness` to require completeness. -/
def executeSelected (graph : SelectedGraph) (inputs : Array Nat)
    (commitment : Nat) : Except String Assignment := do
  if !graph.layoutValid || inputs.size != 49 then
    throw "Pinned witness graph or input prefix has the wrong shape."
  if inputs[0]! != 1 then throw "Witness constant slot must equal one."
  let mut state := Assignment.empty graph.nSignals
  for i in [0:49] do state ← state.write i inputs[i]!
  state ← state.write graph.commitmentSignal commitment
  for component in graph.num2bits do state ← executeNum2Bits state component
  for base in graph.bases do state ← state.write base.index base.value
  for primitive in graph.primitives do
    state ← evaluatePrimitive state primitive
  let constants := mimcConstants
  for i in [0:20] do
    state ← executeMerkleLevel constants state graph.merkle[i]! graph.feistel[i]!
  let expectedRoot ← state.read graph.rootSignal
  let computedRoot ← state.read graph.merkle[19]!.hashOutput
  if expectedRoot != computedRoot then throw "Merkle root differs from the selected path."
  return state

def assignedWitnessCount (graph : SelectedGraph) (state : Assignment) : Nat :=
  (state.values.extract 0 graph.nVars).filter Option.isSome |>.size

/-- Materialize a complete witness only when every internal Circom signal has
    a native assignment. An unimplemented signal produces an error; there is
    no zero filling or fallback to a JavaScript-generated fixture. -/
def Assignment.toWitness (graph : SelectedGraph) (state : Assignment) :
    Except String (Array Nat) := do
  if !graph.layoutValid || state.values.size != graph.nSignals then
    throw "Witness graph or signal vector has the wrong shape."
  for i in [0:graph.nSignals] do
    if (state.values[i]!).isNone then
      throw s!"Internal circuit signal {i} has not been computed."
  let mut witness := #[]
  for i in [0:graph.nVars] do
    witness := witness.push (← state.read i)
  return witness

/-- Append ASCII decimal fields directly to a byte array. Building one large
    string by repeated concatenation would be quadratic for this circuit. -/
private def appendText (bytes : ByteArray) (value : String) : ByteArray := Id.run do
  let mut out := bytes
  for byte in value.toUTF8.data do out := out.push byte
  return out

/-- Stable serialization of one sparse R1CS row, independent of the order in
    which a JSON decoder visited its signal-index keys. -/
private def appendCanonicalRow (bytes : ByteArray)
    (row : LinearCombination) : ByteArray := Id.run do
  let mut out := bytes
  let sorted := row.terms.qsort (fun left right => left.1 < right.1)
  for i in [0:sorted.size] do
    if i > 0 then out := out.push 44
    out := appendText out s!"{sorted[i]!.1}:{sorted[i]!.2}"
  return out

/-- SHA-256 of the decoded constraints and public dimensions. The expected
    value was independently computed from the SHA-256-pinned source circuit by
    `witness-vm-extract.mjs`. This prevents a same-sized substituted R1CS from
    passing the final checked-witness API. -/
def canonicalCircuitSHA256 (circuit : Circuit) : String := Id.run do
  let mut bytes := appendText ByteArray.empty
    s!"{circuit.nVars}/{circuit.nPublic}/{circuit.constraints.size}\n"
  for i in [0:circuit.constraints.size] do
    if i > 0 then bytes := bytes.push 10
    let constraint := circuit.constraints[i]!
    bytes := appendCanonicalRow bytes constraint.a
    bytes := (appendCanonicalRow (bytes.push 124) constraint.b)
    bytes := (appendCanonicalRow (bytes.push 124) constraint.c)
  return sha256Hex bytes

def pinnedCircuitCanonicalSHA256 : String :=
  "8e009dc9070dbaa70a9b803e3ec31f18b47b7ec437ba39535dd003f7d848036b"

/-- A decoded R1CS whose dimensions and exact constraint digest were checked.
    The private constructor prevents callers from skipping authentication;
    the proof fields make these properties kernel visible. -/
structure PinnedCircuit where
  private mk ::
  circuit : Circuit
  dimensions : circuit.nVars = 28300 ∧ circuit.nPublic = 6 ∧
    circuit.constraints.size = 28275
  digest : canonicalCircuitSHA256 circuit = pinnedCircuitCanonicalSHA256

/-- Authenticate the decoded constraints once, before producing any witness.
    Subsequent native witness checks can share the certified circuit value. -/
def authenticatePinnedCircuit (circuit : Circuit) : Except String PinnedCircuit :=
  if dimensions : circuit.nVars = 28300 ∧ circuit.nPublic = 6 ∧
      circuit.constraints.size = 28275 then
    if digest : canonicalCircuitSHA256 circuit = pinnedCircuitCanonicalSHA256 then
      .ok ⟨circuit, dimensions, digest⟩
    else .error "The proving circuit constraints differ from the pinned R1CS."
  else .error "The proving circuit has unexpected dimensions."

/-- Complete the native witness only after checking every R1CS equation.
    The `PinnedCircuit` argument already certifies the exact constraints. -/
def finishCheckedWitness (pinnedGraph : PinnedGraph) (pinned : PinnedCircuit)
    (state : Assignment) : Except String (Array Nat) :=
  match state.toWitness pinnedGraph.graph with
  | .error error => .error error
  | .ok witness =>
    match checkCircuit pinned.circuit witness with
    | .error error => .error error
    | .ok checked =>
      if checked == 28275 then .ok witness
      else .error "The proving circuit was not completely checked."

/-- Execute native templates and check every equation of the authenticated
    pinned R1CS before returning a fully native witness. -/
def generateCheckedWitness (pinnedGraph : PinnedGraph) (pinned : PinnedCircuit)
    (inputs : Array Nat) (commitment : Nat) : Except String (Array Nat) :=
  match executeSelected pinnedGraph.graph inputs commitment with
  | .error error => .error error
  | .ok state => finishCheckedWitness pinnedGraph pinned state

theorem finishCheckedWitness_passes (pinnedGraph : PinnedGraph)
    (pinned : PinnedCircuit) (state : Assignment) (witness : Array Nat)
    (h : finishCheckedWitness pinnedGraph pinned state = .ok witness) :
    checkCircuit pinned.circuit witness = .ok 28275 := by
  unfold finishCheckedWitness at h
  cases hw : state.toWitness pinnedGraph.graph with
  | error error => simp [hw] at h
  | ok result =>
    cases hc : checkCircuit pinned.circuit result with
    | error error => simp [hw, hc] at h
    | ok checked =>
      by_cases hn : checked = 28275
      · simp [hw, hc, hn] at h
        cases h
        simpa [hn] using hc
      · simp [hw, hc, hn] at h

/-- Every witness accepted by the final native API has actually passed the
    native complete R1CS checker. This theorem is about the executable Lean
    gate; it does not prove the pinned circuit or Groth16 protocol sound. -/
theorem generateCheckedWitness_passes (pinnedGraph : PinnedGraph)
    (pinned : PinnedCircuit) (inputs : Array Nat) (commitment : Nat)
    (witness : Array Nat)
    (h : generateCheckedWitness pinnedGraph pinned inputs commitment = .ok witness) :
    checkCircuit pinned.circuit witness = .ok 28275 := by
  unfold generateCheckedWitness at h
  cases he : executeSelected pinnedGraph.graph inputs commitment with
  | error error => simp [he] at h
  | ok state =>
    exact finishCheckedWitness_passes pinnedGraph pinned state witness (by simpa [he] using h)

end Tornado.Protocol.WitnessVM

#print axioms Tornado.Protocol.WitnessVM.bitValue_is_binary
#print axioms Tornado.Protocol.WitnessVM.dualMux_zero
#print axioms Tornado.Protocol.WitnessVM.dualMux_one
#print axioms Tornado.Protocol.WitnessVM.finishCheckedWitness_passes
#print axioms Tornado.Protocol.WitnessVM.generateCheckedWitness_passes
