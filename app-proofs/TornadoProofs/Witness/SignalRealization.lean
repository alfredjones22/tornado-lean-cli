import Tornado.Protocol.WitnessGraphCertificate
import TornadoProofs.Witness.AssignmentExecution
import TornadoProofs.Witness.SymbolicValues

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic

/-- The concrete partial assignment prescribed by independently interpreted
public DAG nodes. The production VM still performs its original checked writes. -/
def realize (state : SignalState) (values : Array Nat) : Assignment :=
  ⟨state.slots.map fun slot => slot.map (values[·]!)⟩

def AliasesValid (state : SignalState) (values : Array Nat) : Prop :=
  ∀ pair ∈ state.commitmentAliases.toList, values[pair.1]! = values[pair.2]!

theorem realize_size (state : SignalState) (values : Array Nat) :
    (realize state values).values.size = state.slots.size := by
  simp [realize]

theorem realize_slot (state : SignalState) (values : Array Nat) (index : Nat)
    (bound : index < state.slots.size) :
    (realize state values).values[index]! = (state.slots[index]!).map (values[·]!) := by
  simp [realize, getElem!_pos, bound]

theorem signalRead_realize (state : SignalState) (values : Array Nat)
    (index node : Nat) (read : state.read index = .ok node) :
    (realize state values).read index = .ok values[node]! := by
  by_cases bound : index >= state.slots.size
  · simp [SignalState.read, bound, bind, Except.bind] at read
  have inBounds : index < state.slots.size := by omega
  cases slot : state.slots[index]! with
  | none => simp [SignalState.read, bound, slot, bind, Except.bind, pure, Except.pure] at read
  | some prior =>
    have equal : prior = node := by
      simpa [SignalState.read, bound, slot, bind, Except.bind, pure, Except.pure] using read
    subst prior
    simp [Assignment.read, realize_size, Nat.not_le_of_lt inBounds,
      realize_slot state values index inBounds, slot, bind, Except.bind, pure, Except.pure]

theorem signalWrite_realize (state next : SignalState) (values : Array Nat)
    (index node : Nat) (written : state.write index node = .ok next)
    (bounded : values[node]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (aliases : AliasesValid next values) :
    (realize state values).write index values[node]! = .ok (realize next values) := by
  by_cases out : index >= state.slots.size
  · simp [SignalState.write, out, bind, Except.bind] at written
  have bound : index < state.slots.size := by omega
  have nativeOut : ¬ index >= (realize state values).values.size := by
    simpa only [realize_size] using out
  have nativeBound : ¬ values[node]! >= Tornado.Protocol.Groth16R1CS.scalarPrime := by omega
  have nativeSlot := realize_slot state values index bound
  cases slot : state.slots[index]! with
  | none =>
    simp only [SignalState.write, out, ↓reduceIte, slot, pure, Except.pure] at written
    cases written
    have nativeEmpty : (realize state values).values[index]! = none := by
      simpa only [slot, Option.map_none] using nativeSlot
    have result : realize {state with slots := state.slots.set! index (some node)} values =
        ⟨(realize state values).values.set! index (some values[node]!)⟩ := by
      simp [realize, Array.map_setIfInBounds]
    rw [result]
    simp only [Assignment.write, nativeOut, nativeBound, ↓reduceIte, nativeEmpty,
      bind, Except.bind, pure, Except.pure]
  | some prior =>
    by_cases same : prior = node
    · subst prior
      simp [SignalState.write, out, slot, bind, Except.bind, pure, Except.pure] at written
      cases written
      have nativeSame : (realize state values).values[index]! = some values[node]! := by
        simpa only [slot, Option.map_some] using nativeSlot
      simp only [Assignment.write, nativeOut, nativeBound, ↓reduceIte, nativeSame,
        bne_self_eq_false, Bool.false_eq_true, bind, Except.bind, pure, Except.pure]
    · by_cases commitment : index = 49
      · subst index
        simp only [SignalState.write, out, ↓reduceIte, slot,
          show (prior == node) = false from beq_eq_false_iff_ne.mpr same,
          Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, pure, Except.pure] at written
        cases written
        have equal : values[prior]! = values[node]! := aliases (prior,node) (by simp)
        have nativeSame : (realize state values).values[49]! = some values[node]! := by
          simpa only [slot, Option.map_some, equal] using nativeSlot
        change (realize state values).write 49 values[node]! = .ok (realize state values)
        simp only [Assignment.write, nativeOut, nativeBound, ↓reduceIte, nativeSame,
          bne_self_eq_false, Bool.false_eq_true, bind, Except.bind, pure, Except.pure]
      · simp [SignalState.write, out, slot, same, commitment,
          bind, Except.bind, pure, Except.pure] at written

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.realize_size
#print axioms TornadoProofs.Witness.Execution.realize_slot
#print axioms TornadoProofs.Witness.Execution.signalRead_realize
#print axioms TornadoProofs.Witness.Execution.signalWrite_realize
