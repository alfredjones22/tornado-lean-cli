import TornadoProofs.Witness.LayoutMeaning

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

theorem graph_layout_counts (graph : SelectedGraph) (layout : graph.layoutValid=true) :
    graph.num2bits.size=2 ∧ graph.merkle.size=20 ∧ graph.feistel.size=20 := by
  have checked := (graphLayout_checked graph layout).1
  constructor
  · by_contra different
    simp [graphHeaderBad,different] at checked
  constructor
  · by_contra different
    simp [graphHeaderBad,different] at checked
  · by_contra different
    simp [graphHeaderBad,different] at checked

theorem graph_bit_routing (graph : SelectedGraph) (layout : graph.layoutValid=true) (index : Nat) (bound : index<2) :
    graph.num2bits[index]!.input=7+index ∧ graph.num2bits[index]!.outputs.size=248 := by
  have checked := List.all_eq_true.mp (graphLayout_checked graph layout).2.1 index (List.mem_range.mpr bound)
  constructor
  · by_contra different
    have invalid : graphBitBad graph index=true := by simp [graphBitBad,different]
    simp only [invalid,Bool.not_true] at checked
    contradiction
  · by_contra different
    have invalid : graphBitBad graph index=true := by simp [graphBitBad,different]
    simp only [invalid,Bool.not_true] at checked
    contradiction

theorem graph_merkle_routing (graph : SelectedGraph) (layout : graph.layoutValid=true) (index : Nat) (bound : index<20) :
    graph.merkle[index]!.leftInput=(if index=0 then graph.commitmentSignal else graph.merkle[index-1]!.hashOutput) ∧
    graph.merkle[index]!.rightInput=9+index ∧ graph.merkle[index]!.selector=29+index := by
  have checked := List.all_eq_true.mp (graphLayout_checked graph layout).2.2.1 index (List.mem_range.mpr bound)
  constructor
  · by_contra different
    have invalid : graphMerkleBad graph index=true := by simpa only [beq_iff_eq] using
      (show graphMerkleBad graph index=true from by simp [graphMerkleBad,different])
    simp only [invalid,Bool.not_true] at checked
    contradiction
  constructor
  · by_contra different
    have invalid : graphMerkleBad graph index=true := by simp [graphMerkleBad,different]
    simp only [invalid,Bool.not_true] at checked
    contradiction
  · by_contra different
    have invalid : graphMerkleBad graph index=true := by simp [graphMerkleBad,different]
    simp only [invalid,Bool.not_true] at checked
    contradiction

theorem source_bits_admitted (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (inputs : Array Nat) (commitment : Nat)
    (size : inputs.size=49) (constant : inputs[0]! = 1)
    (nullifierBound : inputs[7]! < 2^248) (secretBound : inputs[8]! < 2^248) :
    ∀ component∈graph.num2bits,BitSourceAdmitted compiled (sourceValues resolver inputs commitment) component := by
  intro component member
  obtain ⟨index,bound,equal⟩ := Array.mem_iff_getElem.mp member
  have count := (graph_layout_counts graph trace.layout).1
  have small : index<2 := by simpa only [count] using bound
  have routing := (graph_bit_routing graph trace.layout index small).1
  have componentInput : component.input=7+index := by
    simpa only [getElem!_pos graph.num2bits index bound,equal] using routing
  unfold BitSourceAdmitted
  rw [componentInput,source_prefix_meaning resolver graph compiled trace inputs commitment size constant (7+index) (by omega)]
  have cases : index=0 ∨ index=1 := by omega
  rcases cases with equal | equal <;> subst index
  · exact nullifierBound
  · exact secretBound

theorem source_selectors_admitted (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (inputs : Array Nat) (commitment : Nat)
    (size : inputs.size=49) (constant : inputs[0]! = 1)
    (binary : ∀ index<20,inputs[29+index]! ≤ 1) :
    ∀ index<20,MerkleSourceAdmitted compiled (sourceValues resolver inputs commitment) graph.merkle[index]! := by
  intro index bound
  unfold MerkleSourceAdmitted
  rw [(graph_merkle_routing graph trace.layout index bound).2.2,
    source_prefix_meaning resolver graph compiled trace inputs commitment size constant (29+index) (by omega)]
  exact binary index bound

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.graph_layout_counts
#print axioms TornadoProofs.Witness.Execution.graph_bit_routing
#print axioms TornadoProofs.Witness.Execution.graph_merkle_routing
#print axioms TornadoProofs.Witness.Execution.source_bits_admitted
#print axioms TornadoProofs.Witness.Execution.source_selectors_admitted
