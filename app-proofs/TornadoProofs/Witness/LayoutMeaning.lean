import TornadoProofs.Witness.CommitmentMeaning

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM

abbrev GuardFrame := MProd (Option Bool) PUnit.{1}

def guardStep (bad : Nat → Bool) (index : Nat) (_ : GuardFrame) : Id (ForInStep GuardFrame) :=
  if bad index then pure (.done ⟨some false,PUnit.unit⟩)
  else pure (.yield ⟨none,PUnit.unit⟩)

theorem guard_loop_value (items : List Nat) (bad : Nat → Bool) :
    (forIn items (⟨none,PUnit.unit⟩ : GuardFrame) (guardStep bad) : Id GuardFrame).run =
      (if items.all (fun index => !bad index) then ⟨none,PUnit.unit⟩ else ⟨some false,PUnit.unit⟩) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    cases checked : bad head with
    | false => simpa [List.forIn_cons,guardStep,checked] using ih
    | true => simp [List.forIn_cons,guardStep,checked]

def graphHeaderBad (graph : SelectedGraph) : Bool :=
  graph.nSignals != 36528 || graph.nVars != 28300 ||
    graph.commitmentSignal != 49 || graph.rootSignal != 1 ||
    graph.num2bits.size != 2 || graph.merkle.size != 20 ||
    graph.feistel.size != 20 || graph.bases.size != 10 || graph.primitives.size != 2234

def graphBitBad (graph : SelectedGraph) (index : Nat) : Bool :=
  let component := graph.num2bits[index]!
  component.name != (if index==0 then "main.hasher.nullifierBits" else "main.hasher.secretBits") ||
    component.input != 7+index || component.outputs.size != 248 ||
    component.outputs.any (· >= graph.nSignals)

def graphMerkleBad (graph : SelectedGraph) (index : Nat) : Bool :=
  let level := graph.merkle[index]!
  let previous := if index==0 then graph.commitmentSignal else graph.merkle[index-1]!.hashOutput
  let sponge := graph.feistel[index]!
  (level.level != index || level.leftInput != previous || level.rightInput != 9+index ||
    level.selector != 29+index || level.leftOutput >= graph.nSignals ||
    level.rightOutput >= graph.nSignals || level.hashOutput >= graph.nSignals) ||
    (!sponge.first.layoutValid graph.nSignals || !sponge.second.layoutValid graph.nSignals ||
      sponge.first.key != sponge.second.key || sponge.first.leftInput != level.leftOutput ||
      sponge.second.rightInput != sponge.first.rightOutput || sponge.second.leftOutput != level.hashOutput)

def graphMerkleGuard (graph : SelectedGraph) (index : Nat) (_ : GuardFrame) : Id (ForInStep GuardFrame) := do
  let level := graph.merkle[index]!
  let previous := if index==0 then graph.commitmentSignal else graph.merkle[index-1]!.hashOutput
  if level.level != index || level.leftInput != previous || level.rightInput != 9+index ||
      level.selector != 29+index || level.leftOutput >= graph.nSignals ||
      level.rightOutput >= graph.nSignals || level.hashOutput >= graph.nSignals then
    pure (.done ⟨some false,PUnit.unit⟩)
  else
    let sponge := graph.feistel[index]!
    if !sponge.first.layoutValid graph.nSignals || !sponge.second.layoutValid graph.nSignals ||
        sponge.first.key != sponge.second.key || sponge.first.leftInput != level.leftOutput ||
        sponge.second.rightInput != sponge.first.rightOutput || sponge.second.leftOutput != level.hashOutput then
      pure (.done ⟨some false,PUnit.unit⟩)
    else pure (.yield ⟨none,PUnit.unit⟩)

def graphTailBad (graph : SelectedGraph) : Bool :=
  graph.bases.any (fun base => base.index >= graph.nSignals || base.value >= Tornado.Protocol.Groth16R1CS.scalarPrime) ||
    graph.primitives.any (fun item => !item.shapeValid graph.nSignals)

def graphLayoutBody (graph : SelectedGraph) : Bool :=
  if graphHeaderBad graph then false else
    let bits := (forIn (List.range 2) (⟨none,PUnit.unit⟩ : GuardFrame) (guardStep (graphBitBad graph)) : Id GuardFrame).run
    match bits.fst with
    | none =>
      let merkle := (forIn (List.range 20) (⟨none,PUnit.unit⟩ : GuardFrame) (graphMerkleGuard graph) : Id GuardFrame).run
      match merkle.fst with
      | none => if graphTailBad graph then false else true
      | some value => value
    | some value => value

theorem graphLayout_source (graph : SelectedGraph) : graph.layoutValid=graphLayoutBody graph := by
  unfold SelectedGraph.layoutValid graphLayoutBody
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,
    Nat.add_sub_cancel,Nat.div_one,←List.range_eq_range']
  unfold graphHeaderBad graphBitBad graphMerkleGuard graphTailBad guardStep
  simp only [Id.run,pure,bind]
  rfl

theorem merkleGuard_source (graph : SelectedGraph) : graphMerkleGuard graph=guardStep (graphMerkleBad graph) := by
  funext index frame
  unfold graphMerkleGuard guardStep graphMerkleBad
  simp only [Bool.or_eq_true,ite_or]

theorem graphLayout_checked (graph : SelectedGraph) (layout : graph.layoutValid=true) :
    graphHeaderBad graph=false ∧ (List.range 2).all (fun index => !graphBitBad graph index)=true ∧
      (List.range 20).all (fun index => !graphMerkleBad graph index)=true ∧ graphTailBad graph=false := by
  rw [graphLayout_source] at layout
  unfold graphLayoutBody at layout
  rw [merkleGuard_source,guard_loop_value,guard_loop_value] at layout
  cases header : graphHeaderBad graph <;>
    cases bits : (List.range 2).all (fun index => !graphBitBad graph index) <;>
    cases merkle : (List.range 20).all (fun index => !graphMerkleBad graph index) <;>
    cases tail : graphTailBad graph <;>
    simp_all

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.guard_loop_value
#print axioms TornadoProofs.Witness.Execution.graphLayout_source
#print axioms TornadoProofs.Witness.Execution.merkleGuard_source
#print axioms TornadoProofs.Witness.Execution.graphLayout_checked
