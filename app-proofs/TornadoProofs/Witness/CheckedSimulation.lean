import TornadoProofs.Witness.SignalRealization

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution

def stepValue {S : Type} : ForInStep S → S
  | .done state | .yield state => state

def mapStep {S T : Type} (realizeState : S → T) : ForInStep S → ForInStep T
  | .done state => .done (realizeState state)
  | .yield state => .yield (realizeState state)

/-- Construct actual execution from a successful public metadata compilation.
The terminal predicate may flow backwards (for example, every accumulated
commitment alias has equal independently interpreted values). No successful
secret execution or final constraint checker is assumed. -/
theorem forIn_construct_from_public {A S T : Type}
    (items : List A) (publicStep : A → S → Except String (ForInStep S))
    (actualStep : A → T → Except String (ForInStep T)) (realizeState : S → T)
    (admitted : S → Prop)
    (backwards : ∀ item before step, publicStep item before = .ok step →
      admitted (stepValue step) → admitted before)
    (construct : ∀ item before step, publicStep item before = .ok step →
      admitted (stepValue step) →
      actualStep item (realizeState before) = .ok (mapStep realizeState step))
    (initial final : S) (compiled : forIn items initial publicStep = .ok final)
    (terminal : admitted final) :
    admitted initial ∧ forIn items (realizeState initial) actualStep = .ok (realizeState final) := by
  induction items generalizing initial final with
  | nil =>
    have equal : initial = final := by
      simpa only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] using compiled
    subst final
    exact ⟨terminal,rfl⟩
  | cons item rest ih =>
    cases first : publicStep item initial with
    | error err => simp [List.forIn_cons, first, bind, Except.bind] at compiled
    | ok step =>
      cases step with
      | done middle =>
        have equal : middle = final := by
          simpa only [List.forIn_cons, first, bind, Except.bind, pure, Except.pure,
            Except.ok.injEq] using compiled
        subst final
        have runtime := construct item initial (.done middle) first terminal
        refine ⟨backwards item initial (.done middle) first terminal, ?_⟩
        simp only [List.forIn_cons, runtime, mapStep, bind, Except.bind, pure, Except.pure]
      | yield middle =>
        cases tail : forIn rest middle publicStep with
        | error err => simp [List.forIn_cons, first, tail, bind, Except.bind] at compiled
        | ok result =>
          have equal : result = final := by
            simpa only [List.forIn_cons, first, tail, bind, Except.bind, Except.ok.injEq] using compiled
          subst result
          rcases ih middle final tail terminal with ⟨middleAdmitted,runtimeTail⟩
          have runtime := construct item initial (.yield middle) first middleAdmitted
          refine ⟨backwards item initial (.yield middle) first middleAdmitted, ?_⟩
          simpa only [List.forIn_cons, runtime, mapStep, bind, Except.bind] using runtimeTail

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.forIn_construct_from_public
