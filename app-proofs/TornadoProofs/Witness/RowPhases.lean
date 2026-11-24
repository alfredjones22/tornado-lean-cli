import TornadoProofs.Witness.PrimitivePhases

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution

theorem action_loop_backwards {A S : Type} (items : List A)
    (action : A → S → Except String S) (predicate : S → Prop)
    (backwards : ∀ item∈items,∀ before after,action item before=.ok after → predicate after → predicate before)
    (before after : S)
    (compiled : forIn items before (fun item state => do
      let next ← action item state
      pure (ForInStep.yield next))=.ok after)
    (terminal : predicate after) : predicate before := by
  have result := forIn_construct_from_public_mem items _ _ id predicate
    (fun item member state next returned valid => by
      obtain ⟨middle,built,rest⟩ := bind_success (action item state) _ next returned
      have equal : ForInStep.yield middle=next := Except.ok.inj rest
      subst next
      exact backwards item member state middle built valid)
    (fun _ _ _ next returned _ => by cases next <;> simpa only [mapStep,id_eq] using returned)
    before after compiled terminal
  exact result.1

theorem row_phase_sound {A S R : Type} (items : List A)
    (publicAction : A → S → Except String S) (rowAction : A → R → Except String R)
    (predicate : S → Prop) (satisfied : R → Prop)
    (backwards : ∀ item∈items,∀ before after,publicAction item before=.ok after → predicate after → predicate before)
    (stepSound : ∀ item∈items,∀ before after,publicAction item before=.ok after → predicate after →
      ∀ seed result,rowAction item seed=.ok result → satisfied seed → satisfied result)
    (before after : S) (seed result : R)
    (compiled : forIn items before (fun item state => do
      let next ← publicAction item state
      pure (ForInStep.yield next))=.ok after)
    (generated : forIn items seed (fun item state => do
      let next ← rowAction item state
      pure (ForInStep.yield next))=.ok result)
    (terminal : predicate after) (valid : satisfied seed) : satisfied result := by
  induction items generalizing before seed with
  | nil =>
    have equal : seed=result := Except.ok.inj generated
    simpa only [←equal] using valid
  | cons item tail ih =>
    rw [List.forIn_cons] at compiled generated
    simp only [bind_assoc,pure_bind] at compiled generated
    obtain ⟨publicNext,publicBuilt,compiled⟩ := bind_success (publicAction item before) _ after compiled
    simp only [pure,Except.pure,bind,Except.bind] at compiled
    change forIn tail publicNext (fun item state => do
      let next ← publicAction item state
      pure (ForInStep.yield next))=.ok after at compiled
    obtain ⟨rowNext,rowBuilt,generated⟩ := bind_success (rowAction item seed) _ result generated
    simp only [pure,Except.pure,bind,Except.bind] at generated
    change forIn tail rowNext (fun item state => do
      let next ← rowAction item state
      pure (ForInStep.yield next))=.ok result at generated
    have tailBackwards : ∀ next∈tail,∀ before after,
        publicAction next before=.ok after → predicate after → predicate before :=
      fun next member => backwards next (by simp [member])
    have middle := action_loop_backwards tail publicAction predicate tailBackwards
      publicNext after compiled terminal
    have nextValid := stepSound item (by simp) before publicNext publicBuilt middle
      seed rowNext rowBuilt valid
    apply ih tailBackwards (fun next member => stepSound next (by simp [member]))
      publicNext rowNext compiled generated nextValid

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.action_loop_backwards
#print axioms TornadoProofs.Witness.Execution.row_phase_sound
