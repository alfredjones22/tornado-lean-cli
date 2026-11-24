import TornadoProofs.Witness.CheckedSimulation

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution

theorem forIn_construct_from_public_mem {A S T : Type}
    (items : List A) (publicStep : A → S → Except String (ForInStep S))
    (actualStep : A → T → Except String (ForInStep T)) (realizeState : S → T)
    (admitted : S → Prop)
    (backwards : ∀ item ∈ items, ∀ before step, publicStep item before = .ok step →
      admitted (stepValue step) → admitted before)
    (construct : ∀ item ∈ items, ∀ before step, publicStep item before = .ok step →
      admitted (stepValue step) →
      actualStep item (realizeState before) = .ok (mapStep realizeState step))
    (initial final : S) (compiled : forIn items initial publicStep = .ok final)
    (terminal : admitted final) :
    admitted initial ∧ forIn items (realizeState initial) actualStep = .ok (realizeState final) := by
  induction items generalizing initial final with
  | nil =>
    have equal : initial=final := by
      simpa only [List.forIn_nil,pure,Except.pure,Except.ok.injEq] using compiled
    subst final
    exact ⟨terminal,rfl⟩
  | cons item rest ih =>
    cases first : publicStep item initial with
    | error err => simp [List.forIn_cons,first,bind,Except.bind] at compiled
    | ok step =>
      cases step with
      | done middle =>
        have equal : middle=final := by
          simpa only [List.forIn_cons,first,bind,Except.bind,pure,Except.pure,
            Except.ok.injEq] using compiled
        subst final
        have runtime := construct item (by simp) initial (.done middle) first terminal
        refine ⟨backwards item (by simp) initial (.done middle) first terminal,?_⟩
        simp only [List.forIn_cons,runtime,mapStep,bind,Except.bind,pure,Except.pure]
      | yield middle =>
        cases tail : forIn rest middle publicStep with
        | error err => simp [List.forIn_cons,first,tail,bind,Except.bind] at compiled
        | ok result =>
          have equal : result=final := by
            simpa only [List.forIn_cons,first,tail,bind,Except.bind,Except.ok.injEq] using compiled
          subst result
          have tailBackwards := fun a member => backwards a (List.mem_cons_of_mem item member)
          have tailConstruct := fun a member => construct a (List.mem_cons_of_mem item member)
          rcases ih tailBackwards tailConstruct middle final tail terminal with
            ⟨middleAdmitted,runtimeTail⟩
          have runtime := construct item (by simp) initial (.yield middle) first middleAdmitted
          refine ⟨backwards item (by simp) initial (.yield middle) first middleAdmitted,?_⟩
          simpa only [List.forIn_cons,runtime,mapStep,bind,Except.bind] using runtimeTail

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.forIn_construct_from_public_mem
