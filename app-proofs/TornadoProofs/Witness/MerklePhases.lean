import TornadoProofs.Witness.MerkleMetadata

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

theorem merkle_phase_construct (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (canonical : Primitive.Bounded values)
    (constants : Array Nat) (finalRoots : CompiledGraph) (levels : Array MerkleLevel)
    (sponges : Array SpongeLevel)
    (admitted : ∀ index<20,MerkleSourceAdmitted finalRoots values levels[index]!)
    (state after : SignalState)
    (compiled : forIn (List.range 20) state (fun index current => do
      let next ← compileMerkleLevel resolver constants current levels[index]! sponges[index]!
      pure (ForInStep.yield next))=.ok after)
    (terminal : SourceState finalRoots values after) :
    SourceState finalRoots values state ∧
      forIn (List.range 20) (realize state values) (fun index current => do
        let next ← executeMerkleLevel constants current levels[index]! sponges[index]!
        pure (ForInStep.yield next))=.ok (realize after values) := by
  apply forIn_construct_from_public_mem (List.range 20) _ _ (fun state => realize state values)
    (SourceState finalRoots values) _ _ state after compiled terminal
  · intro index member before next returned terminal
    obtain ⟨middle,built,rest⟩ := bind_success
      (compileMerkleLevel resolver constants before levels[index]! sponges[index]!) _ next returned
    have same : ForInStep.yield middle=next := by simpa only [pure,Except.pure,Except.ok.injEq] using rest
    subst next
    exact (merkle_stage_source_construct resolver inputs values denotes canonical constants finalRoots
      before middle levels[index]! sponges[index]! (admitted index (List.mem_range.mp member)) built terminal).1
  · intro index member before next returned terminal
    obtain ⟨middle,built,rest⟩ := bind_success
      (compileMerkleLevel resolver constants before levels[index]! sponges[index]!) _ next returned
    have same : ForInStep.yield middle=next := by simpa only [pure,Except.pure,Except.ok.injEq] using rest
    subst next
    have actual := (merkle_stage_source_construct resolver inputs values denotes canonical constants finalRoots
      before middle levels[index]! sponges[index]! (admitted index (List.mem_range.mp member)) built terminal).2
    simp only [actual,bind,Except.bind,pure,Except.pure,mapStep]

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.merkle_phase_construct
