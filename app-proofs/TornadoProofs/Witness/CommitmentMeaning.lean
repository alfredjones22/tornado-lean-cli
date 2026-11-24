import TornadoProofs.Witness.PrefixMeaning

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

theorem signalWrite_other_slot (state after : SignalState) (index node other : Nat)
    (different : index≠other) (written : state.write index node=.ok after) :
    after.slots[other]?=state.slots[other]? := by
  by_cases outside : index>=state.slots.size
  · simp [SignalState.write,outside,bind,Except.bind] at written
  cases slot : state.slots[index]! with
  | none =>
    simp only [SignalState.write,outside,↓reduceIte,slot,pure,Except.pure] at written
    cases written
    exact Array.getElem?_setIfInBounds_ne different
  | some prior =>
    by_cases same : prior=node
    · simp [SignalState.write,outside,slot,same,bind,Except.bind,pure,Except.pure] at written
      cases written
      rfl
    · by_cases commitment : index=49
      · subst index
        simp [SignalState.write,outside,slot,same,bind,Except.bind,pure,Except.pure] at written
        cases written
        rfl
      · simp [SignalState.write,outside,slot,same,commitment,bind,Except.bind,pure,Except.pure] at written

theorem signalWrite_empty_assigned (state after : SignalState) (index node : Nat)
    (empty : state.slots[index]?=some none) (written : state.write index node=.ok after) :
    after.slots[index]?=some (some node) := by
  have bound := of_getElem?_eq_some empty
  have slot : state.slots[index]! = none := by
    rw [getElem!_pos state.slots index bound]
    exact Option.some.inj ((Array.getElem?_eq_getElem bound).symm.trans empty)
  simp only [SignalState.write,Nat.not_le_of_lt bound,↓reduceIte,slot,pure,Except.pure] at written
  cases written
  simp [bound]

theorem seedAction_other_slot (resolver : Resolver) (index other : Nat) (different : index≠other)
    (state after : SignalState) (compiled : seedPublicAction resolver index state=.ok after) :
    after.slots[other]?=state.slots[other]? := by
  unfold seedPublicAction at compiled
  split at compiled <;>
    obtain ⟨node,_,written⟩ := bind_success _ _ after compiled <;>
    exact signalWrite_other_slot state after index node other different written

theorem seed_loop_other_slot (resolver : Resolver) (items : List Nat) (other : Nat)
    (different : ∀ index∈items,index≠other) (state after : SignalState)
    (compiled : forIn items state (fun index current => do
      let next ← seedPublicAction resolver index current
      pure (ForInStep.yield next))=.ok after) : after.slots[other]?=state.slots[other]? := by
  apply LeanCrypto.Proofs.ConstraintCertificate.forIn_success_invariant items _
    (fun current => current.slots[other]?=state.slots[other]?) _ state rfl after compiled
  intro index member before previous next returned
  obtain ⟨middle,built,rest⟩ := bind_success (seedPublicAction resolver index before) _ next returned
  have equal : ForInStep.yield middle=next := Except.ok.inj rest
  subst next
  exact (seedAction_other_slot resolver index other (different index member) before middle built).trans previous

theorem graph_layout_publicSignals (graph : SelectedGraph) (layout : graph.layoutValid=true) :
    graph.commitmentSignal=49 ∧ graph.rootSignal=1 := by
  constructor
  · by_contra different
    simp [SelectedGraph.layoutValid,different] at layout
  · by_contra different
    simp [SelectedGraph.layoutValid,different] at layout

theorem trace_commit_final_extends (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) : SignalExtends trace.withCommitment trace.final := by
  have bits : SignalExtends trace.withCommitment trace.withBits := by
    apply action_loop_signalExtends graph.num2bits.toList (fun item state => compileNum2Bits resolver state item)
      (fun item _ before after built => compileNum2Bits_extends resolver before after item built)
    simpa only [Array.forIn_toList] using trace.bitsBuilt
  have bases : SignalExtends trace.withBits trace.withBases := by
    apply action_loop_signalExtends graph.bases.toList (basePublicAction resolver)
      (fun item _ before after built => baseAction_signalExtends resolver item before after built)
    simpa only [Array.forIn_toList] using trace.basesBuilt
  have primitives : SignalExtends trace.withBases trace.withPrimitives := by
    apply action_loop_signalExtends graph.primitives.toList (fun item state => compilePrimitiveStage resolver state item)
      (fun item _ before after built => compilePrimitiveStage_extends resolver before after item built)
    simpa only [Array.forIn_toList] using trace.primitivesBuilt
  have merkle := action_loop_signalExtends (List.range 20)
    (fun index state => compileMerkleLevel resolver Tornado.Crypto.mimcConstants state graph.merkle[index]! graph.feistel[index]!)
    (fun item _ before after built => compileMerkleLevel_signalExtends resolver Tornado.Crypto.mimcConstants before after _ _ built)
    trace.withPrimitives trace.final trace.merkleBuilt
  exact signalExtends_trans (signalExtends_trans (signalExtends_trans bits bases) primitives) merkle

theorem trace_commitment_meaning (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (data values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values) : values[compiled.signalRoots[49]!]! = data[49]! := by
  have seedEmpty := seed_loop_other_slot resolver (List.range 49) 49
    (fun index member => by have bound := List.mem_range.mp member; omega) _ _ trace.seedsBuilt
  have size : 49<graph.nSignals := by rw [(graph_layout_dimensions graph trace.layout).1]; decide
  have empty : trace.seeded.slots[49]?=some none := by simpa [SignalState.empty,size] using seedEmpty
  have commitmentBuilt : trace.seeded.write 49 trace.commitmentNode=.ok trace.withCommitment := by
    simpa only [(graph_layout_publicSignals graph trace.layout).1] using trace.commitmentBuilt
  have assigned := signalWrite_empty_assigned _ _ _ _ empty commitmentBuilt
  have finalAssigned := (trace_commit_final_extends resolver graph compiled trace).2 _ _ assigned
  have node := complete_nodeFits _ _ trace.complete 49 trace.commitmentNode finalAssigned
  rw [node]
  exact Symbolic.resolve_sound resolver data values denotes (.input 49) trace.commitmentNode trace.commitmentResolved

theorem source_commitment_meaning (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (inputs : Array Nat) (commitment : Nat)
    (size : inputs.size=49) :
    (sourceValues resolver inputs commitment)[compiled.signalRoots[49]!]! = commitment := by
  rw [trace_commitment_meaning resolver graph compiled trace (inputs.push commitment) _
    (sourceValues_denotes resolver inputs commitment trace.table)]
  exact pushed_commitment inputs commitment size

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.signalWrite_other_slot
#print axioms TornadoProofs.Witness.Execution.signalWrite_empty_assigned
#print axioms TornadoProofs.Witness.Execution.seedAction_other_slot
#print axioms TornadoProofs.Witness.Execution.seed_loop_other_slot
#print axioms TornadoProofs.Witness.Execution.graph_layout_publicSignals
#print axioms TornadoProofs.Witness.Execution.trace_commit_final_extends
#print axioms TornadoProofs.Witness.Execution.trace_commitment_meaning
#print axioms TornadoProofs.Witness.Execution.source_commitment_meaning
