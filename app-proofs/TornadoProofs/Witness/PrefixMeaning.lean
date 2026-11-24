import TornadoProofs.Witness.CanonicalSource

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

theorem signalWrite_assigned (state after : SignalState) (index node : Nat) (notCommitment : index≠49)
    (written : state.write index node=.ok after) : after.slots[index]?=some (some node) := by
  by_cases outside : index>=state.slots.size
  · simp [SignalState.write,outside,bind,Except.bind] at written
  have bound : index<state.slots.size := by omega
  cases slot : state.slots[index]! with
  | none =>
    simp only [SignalState.write,outside,↓reduceIte,slot,pure,Except.pure] at written
    cases written
    simp [bound]
  | some prior =>
    by_cases same : prior=node
    · subst prior
      simp [SignalState.write,outside,slot,bind,Except.bind,pure,Except.pure] at written
      cases written
      simpa only [Array.getElem?_eq_getElem bound,getElem!_pos state.slots index bound] using congrArg some slot
    · simp [SignalState.write,outside,slot,same,notCommitment,bind,Except.bind,pure,Except.pure] at written

theorem action_loop_signalExtends {A : Type} (items : List A)
    (action : A → SignalState → Except String SignalState)
    (preserves : ∀ item∈items,∀ before after,action item before=.ok after → SignalExtends before after)
    (state after : SignalState)
    (compiled : forIn items state (fun item current => do
      let next ← action item current
      pure (ForInStep.yield next))=.ok after) : SignalExtends state after := by
  apply LeanCrypto.Proofs.ConstraintCertificate.forIn_success_invariant items _ (SignalExtends state) _
    state (signalExtends_refl state) after compiled
  intro item member before extension next returned
  obtain ⟨middle,built,rest⟩ := bind_success (action item before) _ next returned
  have equal : ForInStep.yield middle=next := Except.ok.inj rest
  subst next
  exact signalExtends_trans extension (preserves item member before middle built)

theorem seedAction_signalExtends (resolver : Resolver) (index : Nat) (state after : SignalState)
    (compiled : seedPublicAction resolver index state=.ok after) : SignalExtends state after := by
  unfold seedPublicAction at compiled
  split at compiled <;>
    obtain ⟨node,_,written⟩ := bind_success _ _ after compiled <;>
    exact signalWrite_extends state after index node written

theorem baseAction_signalExtends (resolver : Resolver) (base : BaseSeed) (state after : SignalState)
    (compiled : basePublicAction resolver base state=.ok after) : SignalExtends state after := by
  obtain ⟨node,_,written⟩ := bind_success (resolver.resolve (.constant base.value)) _ after compiled
  exact signalWrite_extends state after base.index node written

theorem trace_seed_final_extends (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) : SignalExtends trace.seeded trace.final := by
  have commit := signalWrite_extends _ _ _ _ trace.commitmentBuilt
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
  exact signalExtends_trans (signalExtends_trans (signalExtends_trans (signalExtends_trans commit bits) bases) primitives) merkle

theorem seedAction_meaning (resolver : Resolver) (data values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values) (index : Nat) (bound : index<49)
    (state after : SignalState) (compiled : seedPublicAction resolver index state=.ok after) :
    ∃ node,after.slots[index]?=some (some node) ∧ values[node]! = (if index=0 then 1 else data[index]!) := by
  unfold seedPublicAction at compiled
  by_cases zero : index=0
  · subst index
    simp only [beq_self_eq_true,↓reduceIte] at compiled
    obtain ⟨node,resolved,written⟩ := bind_success _ _ after compiled
    exact ⟨node,signalWrite_assigned state after 0 node (by decide) written,
      by simpa only [ite_true] using Symbolic.resolve_sound resolver data values denotes (.constant 1) node resolved⟩
  · have nonzero : (index==0)=false := beq_eq_false_iff_ne.mpr zero
    simp only [nonzero,Bool.false_eq_true,↓reduceIte] at compiled
    obtain ⟨node,resolved,written⟩ := bind_success _ _ after compiled
    exact ⟨node,signalWrite_assigned state after index node (by omega) written,
      by simpa only [zero,↓reduceIte] using Symbolic.resolve_sound resolver data values denotes (.input index) node resolved⟩

theorem seed_loop_meaning (resolver : Resolver) (data values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values) (items : List Nat)
    (bounds : ∀ index∈items,index<49) (state after : SignalState)
    (compiled : forIn items state (fun index current => do
      let next ← seedPublicAction resolver index current
      pure (ForInStep.yield next))=.ok after) :
    ∀ index∈items,∃ node,after.slots[index]?=some (some node) ∧
      values[node]! = (if index=0 then 1 else data[index]!) := by
  induction items generalizing state with
  | nil => simp
  | cons index tail ih =>
    rw [List.forIn_cons] at compiled
    simp only [bind_assoc,pure_bind] at compiled
    obtain ⟨middle,built,compiled⟩ := bind_success (seedPublicAction resolver index state) _ after compiled
    have tailBounds : ∀ index∈tail,index<49 := fun index member => bounds index (by simp [member])
    have tailMeaning := ih tailBounds middle compiled
    have tailExtended := action_loop_signalExtends tail (seedPublicAction resolver)
      (fun index _ before after built => seedAction_signalExtends resolver index before after built)
      middle after compiled
    intro other member
    rcases List.mem_cons.mp member with equal | member
    · subst other
      obtain ⟨node,assigned,value⟩ := seedAction_meaning resolver data values denotes index
        (bounds index (by simp)) state middle built
      exact ⟨node,tailExtended.2 index node assigned,value⟩
    · exact tailMeaning other member

theorem trace_prefix_meaning (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (data values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes data values) (index : Nat) (bound : index<49) :
    values[compiled.signalRoots[index]!]! = (if index=0 then 1 else data[index]!) := by
  have fit := nodeFits_backwards compiled trace.seeded trace.final
    (trace_seed_final_extends resolver graph compiled trace) (complete_nodeFits _ _ trace.complete)
  obtain ⟨node,assigned,value⟩ := seed_loop_meaning resolver data values denotes (List.range 49)
    (fun _ member => List.mem_range.mp member) _ _ trace.seedsBuilt index (List.mem_range.mpr bound)
  rw [fit index node assigned,value]

theorem source_prefix_meaning (resolver : Resolver) (graph : SelectedGraph) (compiled : CompiledGraph)
    (trace : CompilationTrace resolver graph compiled) (inputs : Array Nat) (commitment : Nat)
    (size : inputs.size=49) (constant : inputs[0]! = 1) (index : Nat) (bound : index<49) :
    (sourceValues resolver inputs commitment)[compiled.signalRoots[index]!]! = inputs[index]! := by
  rw [trace_prefix_meaning resolver graph compiled trace (inputs.push commitment) _
    (sourceValues_denotes resolver inputs commitment trace.table) index bound]
  split
  · rename_i equal
    simpa only [equal] using constant.symm
  · exact pushed_prefix inputs commitment size index bound

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.signalWrite_assigned
#print axioms TornadoProofs.Witness.Execution.action_loop_signalExtends
#print axioms TornadoProofs.Witness.Execution.seedAction_signalExtends
#print axioms TornadoProofs.Witness.Execution.baseAction_signalExtends
#print axioms TornadoProofs.Witness.Execution.trace_seed_final_extends
#print axioms TornadoProofs.Witness.Execution.seedAction_meaning
#print axioms TornadoProofs.Witness.Execution.seed_loop_meaning
#print axioms TornadoProofs.Witness.Execution.trace_prefix_meaning
#print axioms TornadoProofs.Witness.Execution.source_prefix_meaning
