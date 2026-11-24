import TornadoProofs.Witness.SignalRealization

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic

def SignalExtends (before after : SignalState) : Prop :=
  after.slots.size = before.slots.size ∧
  ∀ (index node : Nat), before.slots[index]? = some (some node) → after.slots[index]? = some (some node)

theorem signalExtends_refl (state : SignalState) : SignalExtends state state :=
  ⟨rfl,fun _ _ assigned => assigned⟩

theorem signalExtends_trans {first middle last : SignalState}
    (left : SignalExtends first middle) (right : SignalExtends middle last) :
    SignalExtends first last :=
  ⟨right.1.trans left.1,fun index node assigned => right.2 index node (left.2 index node assigned)⟩

theorem signalWrite_aliases_mono (state next : SignalState) (index node : Nat)
    (written : state.write index node = .ok next) :
    ∀ pair ∈ state.commitmentAliases.toList, pair ∈ next.commitmentAliases.toList := by
  by_cases out : index >= state.slots.size
  · simp [SignalState.write, out, bind, Except.bind] at written
  cases slot : state.slots[index]! with
  | none =>
    simp [SignalState.write, out, slot, bind, Except.bind, pure, Except.pure] at written
    cases written
    exact fun _ member => member
  | some prior =>
    by_cases same : prior = node
    · simp [SignalState.write, out, slot, same, bind, Except.bind, pure, Except.pure] at written
      cases written
      exact fun _ member => member
    · by_cases commitment : index = 49
      · subst index
        simp [SignalState.write, out, slot, same, bind, Except.bind, pure, Except.pure] at written
        cases written
        exact fun _ member => by simp [member]
      · simp [SignalState.write, out, slot, same, commitment,
          bind, Except.bind, pure, Except.pure] at written

theorem signalWrite_aliases_backwards (state next : SignalState) (values : Array Nat)
    (index node : Nat) (written : state.write index node = .ok next)
    (admitted : AliasesValid next values) : AliasesValid state values := by
  intro pair member
  exact admitted pair (signalWrite_aliases_mono state next index node written pair member)

theorem signalWrite_extends (state next : SignalState) (index node : Nat)
    (written : state.write index node = .ok next) : SignalExtends state next := by
  by_cases out : index >= state.slots.size
  · simp [SignalState.write, out, bind, Except.bind] at written
  have bound : index < state.slots.size := by omega
  cases slot : state.slots[index]! with
  | none =>
    simp [SignalState.write, out, slot, bind, Except.bind, pure, Except.pure] at written
    cases written
    refine ⟨by simp,?_⟩
    intro other prior assigned
    by_cases equal : index = other
    · subst other
      have empty : state.slots[index]? = some none := by
        simpa only [getElem!_pos state.slots index bound, Array.getElem?_eq_getElem bound] using
          congrArg some slot
      simp only [empty, Option.some.injEq, reduceCtorEq] at assigned
    · simpa only [Array.getElem?_setIfInBounds_ne equal] using assigned
  | some prior =>
    by_cases same : prior = node
    · simp [SignalState.write, out, slot, same, bind, Except.bind, pure, Except.pure] at written
      cases written
      exact signalExtends_refl state
    · by_cases commitment : index = 49
      · subst index
        simp [SignalState.write, out, slot, same, bind, Except.bind, pure, Except.pure] at written
        cases written
        exact ⟨rfl,fun _ _ prior => prior⟩
      · simp [SignalState.write, out, slot, same, commitment,
          bind, Except.bind, pure, Except.pure] at written

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.signalExtends_refl
#print axioms TornadoProofs.Witness.Execution.signalExtends_trans
#print axioms TornadoProofs.Witness.Execution.signalWrite_aliases_mono
#print axioms TornadoProofs.Witness.Execution.signalWrite_aliases_backwards
#print axioms TornadoProofs.Witness.Execution.signalWrite_extends
