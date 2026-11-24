import Tornado.Spec.WitnessGadgets

open Tornado.Protocol.WitnessVM Tornado.Protocol.Groth16R1CS

private def require (condition : Bool) (description : String) : IO Unit := do
  unless condition do throw <| IO.userError description

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

private def sameResult (left right : Except String Assignment) : Bool :=
  match left, right with
  | .error left, .error right => left == right
  | .ok left, .ok right => left.values == right.values
  | _, _ => false

private def bitCase (graph : SelectedGraph) (component : Num2BitsComponent) (value : Nat) : IO Unit := do
  let initial ← unwrap <| (Assignment.empty graph.nSignals).write component.input value
  let initial ← unwrap <| initial.write (graph.nSignals - 1) 17
  let final ← unwrap <| executeNum2Bits initial component
  require (final.values.size == graph.nSignals) "Num2Bits changed assignment size"
  require ((← unwrap <| final.read component.input) == value) "Num2Bits changed its original input"
  require ((← unwrap <| final.read (graph.nSignals - 1)) == 17) "Num2Bits changed an unrelated assignment"
  for bit in [0:248] do
    let actual ← unwrap <| final.read component.outputs[bit]!
    require (actual == bitValue value bit && actual * actual == actual)
      "Num2Bits did not assign the graph's exact boolean signal"
    require (actual * ((actual + scalarPrime - 1) % scalarPrime) % scalarPrime == 0)
      "Stored Num2Bits signal violates its exact Fr boolean equation"
  require (storedBitSum final component == value) "Stored bit signals do not reconstruct the input"
  let repeated ← unwrap <| executeNum2Bits final component
  require (repeated.values == final.values) "Consistent signal reassignment changed values"
  let conflict := 1 - bitValue value 0
  let conflictState ← unwrap <| initial.write component.outputs[0]! conflict
  require (!(executeNum2Bits conflictState component).isOk) "Num2Bits accepted a conflicting original slot"

private def muxCase (graph : SelectedGraph) (level : MerkleLevel)
    (selector input0 input1 : Nat) : IO Unit := do
  let initial ← unwrap <| (Assignment.empty graph.nSignals).write level.leftInput input0
  let initial ← unwrap <| initial.write level.rightInput input1
  let initial ← unwrap <| initial.write level.selector selector
  let initial ← unwrap <| initial.write (graph.nSignals - 1) 19
  let (final, left, right) ← unwrap <| executeDualMux initial level
  require (left == (if selector == 0 then input0 else input1) &&
    right == (if selector == 0 then input1 else input0)) "DualMux selected the wrong direction"
  require ((← unwrap <| final.read level.leftOutput) == left &&
    (← unwrap <| final.read level.rightOutput) == right) "DualMux wrote the wrong graph signals"
  require (selector * selector == selector &&
    left + selector * input0 == input0 + selector * input1 &&
    right + selector * input1 == input1 + selector * input0) "DualMux boolean/additive equations failed"
  require (selector * ((1 + scalarPrime - selector) % scalarPrime) % scalarPrime == 0 &&
    (((input1 + scalarPrime - input0) % scalarPrime) * selector + input0) % scalarPrime == left &&
    (((input0 + scalarPrime - input1) % scalarPrime) * selector + input1) % scalarPrime == right)
    "Stored DualMux signals violate their exact Fr equations"
  require ((← unwrap <| final.read level.leftInput) == input0 &&
    (← unwrap <| final.read level.rightInput) == input1 &&
    (← unwrap <| final.read level.selector) == selector &&
    (← unwrap <| final.read (graph.nSignals - 1)) == 19) "DualMux changed original assignments"

def main : IO Unit := do
  let pinned ← unwrap <| decodePinnedGraph (← IO.FS.readFile "fixtures/witness-vm-selected-components.json")
  let graph := pinned.graph
  let mut publicValues := #[0, 1, 2, 3, 2 ^ 247, 2 ^ 248 - 1,
    0x123456789abcdef0123456789abcdef0123456789abcdef]
  let mut nextPublic := 8675309
  for _ in [0:12] do
    nextPublic := (nextPublic * 6364136223846793005 + 1442695040888963407) % (2 ^ 248)
    publicValues := publicValues.push nextPublic
  for component in graph.num2bits do
    for value in publicValues do bitCase graph component value
    let state ← unwrap <| (Assignment.empty graph.nSignals).write component.input (2 ^ 248)
    require (!(executeNum2Bits state component).isOk) "Num2Bits accepted input outside its 248-bit width"
    let state ← unwrap <| (Assignment.empty graph.nSignals).write component.input 0
    require (!(executeNum2Bits state { component with outputs := component.outputs.extract 0 247 }).isOk)
      "Num2Bits accepted malformed component width"
    require (!(executeNum2Bits state { component with outputs := component.outputs.set! 0 graph.nSignals }).isOk)
      "Num2Bits accepted an out-of-bounds graph slot"
    require (!(executeNum2Bits (Assignment.empty graph.nSignals) component).isOk)
      "Num2Bits accepted an uncomputed input"
    let aliasComponent := { component with outputs := component.outputs.set! 1 component.outputs[0]! }
    require ((executeNum2Bits state aliasComponent).isOk) "Num2Bits rejected a consistent alias"
    let one ← unwrap <| (Assignment.empty graph.nSignals).write component.input 1
    require (!(executeNum2Bits one aliasComponent).isOk) "Num2Bits accepted inconsistent bit aliases"
  for width in [0:9] do
    for value in [0:2 ^ width] do
      require (bitSum width value == value) "Exhaustive small-width bit reconstruction failed"
      require (bitSum width (value + 2 ^ width) != value + 2 ^ width)
        "Bit reconstruction negative control failed"
  for i in [0:graph.merkle.size] do
    let level := graph.merkle[i]!
    for selector in [0:2] do
      for pair in #[(0, 0), (1, 0), (0, 1), (11, 29), (scalarPrime - 1, scalarPrime - 2)] do
        muxCase graph level selector pair.1 pair.2
    let bad ← unwrap <| (Assignment.empty graph.nSignals).write level.leftInput 11
    let bad ← unwrap <| bad.write level.rightInput 29
    let bad ← unwrap <| bad.write level.selector 2
    require (!(executeDualMux bad level).isOk) "DualMux accepted a nonbinary selector"
    let good ← unwrap <| (Assignment.empty graph.nSignals).write level.leftInput 11
    let good ← unwrap <| good.write level.rightInput 29
    let good ← unwrap <| good.write level.selector 0
    let conflicting ← unwrap <| good.write level.rightOutput 30
    require (!(executeDualMux conflicting level).isOk) "DualMux accepted a conflicting output"
    -- Empty constants make the downstream Feistel fail quickly. Both the
    -- exact original block and refactored caller must return identical errors.
    require (sameResult (executeMerkleLevel #[] good level graph.feistel[i]!)
      (executeMerkleLevelOriginal #[] good level graph.feistel[i]!)) "Merkle selector factoring changed a failure path"
    require (sameResult (executeMerkleLevel #[] bad level graph.feistel[i]!)
      (executeMerkleLevelOriginal #[] bad level graph.feistel[i]!)) "Merkle selector factoring changed bit rejection"
    require (sameResult (executeMerkleLevel #[] conflicting level graph.feistel[i]!)
      (executeMerkleLevelOriginal #[] conflicting level graph.feistel[i]!)) "Merkle selector factoring changed alias rejection"
  require (!((Assignment.empty 2).write 0 scalarPrime).isOk) "Assignment.write accepted an Fr overflow"
  require (!((Assignment.empty 2).write 2 0).isOk) "Assignment.write accepted an out-of-bounds index"
  IO.println "PASS: actual pinned Num2Bits and DualMux slots, constructive equations, assignment preservation, exhaustive small-width reconstruction, alias conflicts, and refactor error parity"
