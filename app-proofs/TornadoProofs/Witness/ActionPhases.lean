import TornadoProofs.Witness.MetadataState

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic

theorem action_phase_construct {A : Type} (items : Array A)
    (publicAction : A → SignalState → Except String SignalState)
    (actualAction : A → Assignment → Except String Assignment)
    (values : Array Nat) (predicate : SignalState → Prop)
    (construct : ∀ item ∈ items, ∀ before after, publicAction item before=.ok after →
      predicate after → predicate before ∧
        actualAction item (realize before values)=.ok (realize after values))
    (state after : SignalState)
    (compiled : forIn items state (fun item current => do
      let next ← publicAction item current
      pure (ForInStep.yield next))=.ok after)
    (terminal : predicate after) :
    predicate state ∧
      forIn items (realize state values) (fun item current => do
        let next ← actualAction item current
        pure (ForInStep.yield next))=.ok (realize after values) := by
  rw [← Array.forIn_toList] at compiled ⊢
  apply forIn_construct_from_public_mem items.toList _ _ (fun state => realize state values)
    predicate _ _ state after compiled terminal
  · intro item member before next returned terminal
    obtain ⟨middle,run,rest⟩ := bind_success (publicAction item before) _ next returned
    have same : ForInStep.yield middle=next := by
      simpa only [pure,Except.pure,Except.ok.injEq] using rest
    subst next
    exact (construct item (by simpa using member) before middle run terminal).1
  · intro item member before next returned terminal
    obtain ⟨middle,run,rest⟩ := bind_success (publicAction item before) _ next returned
    have same : ForInStep.yield middle=next := by
      simpa only [pure,Except.pure,Except.ok.injEq] using rest
    subst next
    have actual := (construct item (by simpa using member) before middle run terminal).2
    simp only [actual,bind,Except.bind,pure,Except.pure,mapStep]

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.action_phase_construct
