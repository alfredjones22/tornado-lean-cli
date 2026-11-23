import Tornado.Protocol.WitnessVM

open Lean Tornado.Crypto Tornado.Protocol.WitnessVM
open Tornado.Protocol.TornadoWitness Tornado.Protocol.Groth16R1CS

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

private def rowKnown (state : Assignment) (row : LinearCombination) : Bool :=
  row.terms.all (fun (index, _) =>
    index < state.values.size && (state.values[index]!).isSome)

private def coveredConstraint (state : Assignment) (constraint : Constraint) : Bool :=
  rowKnown state constraint.a && rowKnown state constraint.b && rowKnown state constraint.c

def main : IO UInt32 := do
  let graphRaw ← IO.FS.readFile "fixtures/witness-vm-selected-components.json"
  let pinnedGraph ← unwrap "verify and decode pinned graph" <| decodePinnedGraph graphRaw
  let graph := pinnedGraph.graph
  let graphJson ← unwrap "parse selected graph" <| Json.parse graphRaw
  let key := bigEndian
    0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb 32
  let note ← unwrap "derive public test note" <|
    tornadoSignatureNote key 1 0 0x199112eb461ea7eec1d75b33343542e1d069b41c
  let tree ← unwrap "build public one-leaf tree" <| buildMimcTree #[note.commitment]
  let proof ← unwrap "build public membership proof" <| mimcProofAt tree 0
  let input : WithdrawalInput := {
    note, proof, expectedRoot := tree.root,
    recipient := 1, relayer := 0, fee := 0, refund := 0 }
  let inputs ← unwrap "compute checked 49-slot prefix" <| prepareInputPrefix input
  let state ← unwrap "execute selected native templates" <|
    executeSelected graph inputs note.commitment
  require (assignedWitnessCount graph state == 28300)
    "Native templates did not produce all 28,300 R1CS witness slots."
  require ((state.values.filter Option.isSome).size == 36528)
    "Native templates did not produce all 36,528 circuit signals."
  let nativeWitness ← unwrap "materialize complete native witness" <|
    state.toWitness graph
  require (nativeWitness.size == 28300)
    "Complete native witness length differs from the pinned circuit."

  let fixture ← unwrap "parse pinned R1CS fixture" <|
    Json.parse (← IO.FS.readFile "fixtures/groth16-tornado-r1cs.json")
  let witness ← unwrap "decode pinned full witness" <|
    fixture.getObjVal? "witness" >>= decodeWitness
  require (witness.size == graph.nVars) "Pinned witness length changed."
  for index in [0:graph.nVars] do
    if let some value := state.values[index]! then
      require (witness[index]! == value)
        s!"Native selected signal {index} differs from the pinned full witness."

  -- Count and check each R1CS row whose inputs have native assignments. The
  -- required count below confirms that none of the pinned rows were skipped.
  let circuit ← unwrap "decode pinned circuit constraints" <| decodeCircuit fixture
  let pinned ← unwrap "authenticate exact pinned R1CS" <|
    authenticatePinnedCircuit circuit
  let complete := (state.values.extract 0 graph.nVars).map (·.getD 0)
  let mut covered := 0
  for row in circuit.constraints do
    if coveredConstraint state row then
      require (← unwrap "check covered R1CS row" <| checkConstraint complete row)
        "A covered R1CS constraint failed."
      covered := covered + 1
  require (covered == 28275)
    "Native templates did not cover all 28,275 R1CS constraints."
  let checkedWitness ← unwrap "finish checked native witness" <|
    finishCheckedWitness pinnedGraph pinned state
  require (checkedWitness == nativeWitness)
    "Checked native witness differs from its assigned circuit signals."

  let emptyRow : LinearCombination := ⟨#[]⟩
  let emptyConstraint : Constraint := ⟨emptyRow, emptyRow, emptyRow⟩
  let alteredCircuit : Circuit := { circuit with
    constraints := circuit.constraints.set! 0 emptyConstraint }
  require (rejected <| authenticatePinnedCircuit alteredCircuit)
    "Same-sized but modified R1CS constraints were accepted."

  let missingInternal : Assignment :=
    ⟨state.values.set! (graph.nSignals - 1) none⟩
  require (rejected <| missingInternal.toWitness graph)
    "Incomplete internal Circom signals were materialized as a witness."
  require (rejected <| finishCheckedWitness pinnedGraph pinned missingInternal)
    "Incomplete internal Circom signals passed the checked-witness API."

  require (rejected <| state.write 0 0) "Conflicting signal assignment was accepted."
  require (rejected <| executeSelected graph (inputs.set! 1 (tree.root + 1)) note.commitment)
    "Wrong expected root was accepted."
  require (rejected <| executeSelected graph (inputs.set! 29 2) note.commitment)
    "Non-bit Merkle selector was accepted."
  require (rejected <| executeSelected graph (inputs.set! 7 (2 ^ 248)) note.commitment)
    "Out-of-range Num2Bits input was accepted."
  require (rejected <| decodeSelectedGraph
    (match graphJson with
      | .obj obj => .obj (obj.insert "sourceCircuitSha256" (.str "wrong"))
      | _ => graphJson)) "Unpinned graph was accepted."
  require (rejected <| decodePinnedGraph (graphRaw ++ " "))
    "Modified arithmetic graph bytes were accepted."

  -- A second, independently generated path with a nonzero direction bit
  -- checks that the native selector swaps the left/right inputs correctly.
  let treeTwo ← unwrap "build two-leaf tree" <|
    buildMimcTree #[mimcZeroLeaf, note.commitment]
  let proofTwo ← unwrap "build second-leaf path" <| mimcProofAt treeTwo 1
  let inputsTwo ← unwrap "prepare second-leaf prefix" <|
    prepareInputPrefix { input with proof := proofTwo, expectedRoot := treeTwo.root }
  require (inputsTwo[29]! == 1) "Second-leaf direction was not one."
  let second ← unwrap "execute selected templates on second leaf" <|
    executeSelected graph inputsTwo note.commitment
  require ((second.values.filter Option.isSome).size == 36528)
    "Second-leaf path left a circuit signal unassigned."
  require ((← unwrap "first selector output" <| second.read graph.merkle[0]!.leftOutput) ==
    proofTwo.siblings[0]!) "Second-leaf selector did not swap its inputs."
  let secondWitness ← unwrap "finish second-leaf checked witness" <|
    finishCheckedWitness pinnedGraph pinned second
  require (secondWitness.size == 28300)
    "The second-leaf native witness has the wrong length."

  -- Different note material and nonzero public recipient/relayer/fee values
  -- exercise Pedersen, public input placement, and both hash subcircuits.
  let otherNote ← unwrap "derive second public test note" <|
    tornadoSignatureNote key 1 1 0x199112eb461ea7eec1d75b33343542e1d069b41c
  let otherTree ← unwrap "build second-note tree" <|
    buildMimcTree #[otherNote.commitment]
  let otherProof ← unwrap "build second-note path" <|
    mimcProofAt otherTree 0
  let otherInput : WithdrawalInput := {
    note := otherNote, proof := otherProof, expectedRoot := otherTree.root,
    recipient := 0x123, relayer := 0x456, fee := 77, refund := 0 }
  let otherPrefix ← unwrap "prepare second-note inputs" <|
    prepareInputPrefix otherInput
  let otherWitness ← unwrap "generate and check second-note native witness" <|
    generateCheckedWitness pinnedGraph pinned otherPrefix otherNote.commitment
  require (otherWitness.size == 28300)
    "Second-note native witness has the wrong length."

  -- Place the note at the last leaf of a full-depth synthetic tree whose
  -- remaining subtrees are Tornado's canonical zero subtrees. This exercises
  -- the right-hand Merkle branch in all twenty selector instances.
  let mut rightmostRoot := note.commitment
  let mut rightmostSiblings : Array Nat := #[]
  for level in [0:20] do
    let sibling := tree.zeros[level]!
    rightmostSiblings := rightmostSiblings.push sibling
    rightmostRoot ← unwrap "hash rightmost membership level" <|
      mimcHashPairWith mimcConstants sibling rightmostRoot
  let rightmostProof : MimcProof := {
    index := 2 ^ 20 - 1,
    root := rightmostRoot,
    siblings := rightmostSiblings,
    pathIndices := Array.replicate 20 1 }
  let rightmostPrefix ← unwrap "prepare rightmost path inputs" <|
    prepareInputPrefix { input with
      proof := rightmostProof, expectedRoot := rightmostRoot }
  for level in [0:20] do
    require (rightmostPrefix[29 + level]! == 1)
      s!"Rightmost path direction {level} was not one."
  let rightmostWitness ← unwrap "generate and check rightmost native witness" <|
    generateCheckedWitness pinnedGraph pinned rightmostPrefix note.commitment
  require (rightmostWitness.size == 28300)
    "Rightmost native witness has the wrong length."

  IO.println s!"PASS: native Circom templates produced all 28,300 R1CS slots, 36,528 signals, {covered} constraints, and four full-witness R1CS cases"
  return 0
