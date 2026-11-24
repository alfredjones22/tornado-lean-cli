import TornadoProofs.Witness.ScheduleSource
import TornadoProofs.Witness.SpongeSource

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

theorem realized_read_meaning (state : SignalState) (compiled : CompiledGraph) (values : Array Nat)
    (fit : NodeFits compiled state) (index value : Nat)
    (read : (realize state values).read index=.ok value) : value=values[compiled.signalRoots[index]!]! := by
  have assigned := read_assigned_of_success (realize state values) index value read
  have actualBound := of_getElem?_eq_some assigned
  have bound : index<state.slots.size := by simpa only [realize_size] using actualBound
  have actualSlot := assigned_slot (realize state values) index value assigned
  rw [realize_slot state values index bound] at actualSlot
  cases slot : state.slots[index]! with
  | none => simp [slot] at actualSlot
  | some node =>
    have equal : values[node]! = value := by simpa only [slot,Option.map_some,Option.some.injEq] using actualSlot
    have staticSlot : state.slots[index]?=some (some node) := by
      rw [getElem!_pos state.slots index bound] at slot
      simpa only [Array.getElem?_eq_getElem bound] using congrArg some slot
    rw [fit index node staticSlot,equal]

theorem action_loop_observations {A S : Type} (items : List A)
    (action : A → S → Except String S) (predicate : S → Prop) (observation : A → Prop)
    (construct : ∀ item∈items,∀ before after,action item before=.ok after →
      predicate after → predicate before ∧ observation item)
    (before after : S) (compiled : forIn items before (fun item current => do
      let next ← action item current
      pure (ForInStep.yield next))=.ok after) (terminal : predicate after) :
    predicate before ∧ ∀ item∈items,observation item := by
  induction items generalizing before with
  | nil =>
    have equal : before=after := Except.ok.inj compiled
    exact ⟨by simpa only [equal] using terminal,by simp⟩
  | cons item tail ih =>
    rw [List.forIn_cons] at compiled
    simp only [bind_assoc,pure_bind] at compiled
    obtain ⟨middle,built,compiled⟩ := bind_success (action item before) _ after compiled
    have tailResult := ih (fun item member => construct item (by simp [member])) middle compiled
    have first := construct item (by simp) before middle built tailResult.1
    refine ⟨first.1,?_⟩
    intro next member
    rcases List.mem_cons.mp member with equal | member
    · simpa only [equal] using first.2
    · exact tailResult.2 next member

def SlotHash (constants : Array Nat) (compiled : CompiledGraph) (values : Array Nat)
    (level : MerkleLevel) : Prop :=
  let value := fun index => values[compiled.signalRoots[index]!]!
  LeanCrypto.mimcHashPairWith constants (dualMuxValues (value level.selector) (value level.leftInput) (value level.rightInput)).1
    (dualMuxValues (value level.selector) (value level.leftInput) (value level.rightInput)).2=.ok (value level.hashOutput)

theorem merkle_stage_slotHash (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (constants : Array Nat) (compiledGraph : CompiledGraph) (state after : SignalState)
    (level : MerkleLevel) (sponge : SpongeLevel)
    (admitted : MerkleSourceAdmitted compiledGraph values level)
    (compiled : compileMerkleLevel resolver constants state level sponge=.ok after)
    (terminal : SourceState compiledGraph values after) :
    SourceState compiledGraph values state ∧ SlotHash constants compiledGraph values level := by
  have fit := nodeFits_backwards compiledGraph state after
    (compileMerkleLevel_signalExtends resolver constants state after level sponge compiled) terminal.2
  have selector : SelectorBit state level values := by
    intro node read
    rw [←fit level.selector node (signalRead_slot state level.selector node read)]
    exact admitted
  obtain ⟨left,right,bit,hash,leftRead,rightRead,bitRead,_,hashed,stored⟩ :=
    compileMerkleLevel_source_hash resolver inputs values denotes canonical constants state after level sponge
      compiled selector terminal.1
  have source := (merkle_stage_source_construct resolver inputs values denotes canonical constants compiledGraph
    state after level sponge admitted compiled terminal).1
  have leftValue := fit level.leftInput left (signalRead_slot state _ _ leftRead)
  have rightValue := fit level.rightInput right (signalRead_slot state _ _ rightRead)
  have bitValue := fit level.selector bit (signalRead_slot state _ _ bitRead)
  have outputValue := realized_read_meaning after compiledGraph values terminal.2 level.hashOutput hash stored
  refine ⟨source,?_⟩
  unfold SlotHash
  simpa only [leftValue,rightValue,bitValue,←outputValue] using hashed

theorem merkle_phase_slotHashes (resolver : Resolver) (graph : SelectedGraph) (compiledGraph : CompiledGraph)
    (trace : CompilationTrace resolver graph compiledGraph) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (admitted : ∀ index<20,MerkleSourceAdmitted compiledGraph values graph.merkle[index]!)
    (aliases : AliasesValid trace.final values) :
    ∀ index<20,SlotHash Tornado.Crypto.mimcConstants compiledGraph values graph.merkle[index]! := by
  have terminal : SourceState compiledGraph values trace.final :=
    ⟨aliases,complete_nodeFits _ _ trace.complete⟩
  have observed := action_loop_observations (List.range 20)
    (fun index state => compileMerkleLevel resolver Tornado.Crypto.mimcConstants state graph.merkle[index]! graph.feistel[index]!)
    (SourceState compiledGraph values) (fun index => SlotHash Tornado.Crypto.mimcConstants compiledGraph values graph.merkle[index]!)
    (fun index member before after built valid => merkle_stage_slotHash resolver inputs values denotes canonical
      Tornado.Crypto.mimcConstants compiledGraph before after graph.merkle[index]! graph.feistel[index]!
      (admitted index (List.mem_range.mp member)) built valid)
    trace.withPrimitives trace.final trace.merkleBuilt terminal
  exact fun index bound => observed.2 index (List.mem_range.mpr bound)

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.realized_read_meaning
#print axioms TornadoProofs.Witness.Execution.action_loop_observations
#print axioms TornadoProofs.Witness.Execution.merkle_stage_slotHash
#print axioms TornadoProofs.Witness.Execution.merkle_phase_slotHashes
