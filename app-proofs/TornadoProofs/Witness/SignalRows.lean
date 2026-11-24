import TornadoProofs.Witness.LocalConstraints
import TornadoProofs.Witness.SignalMonotone
import TornadoProofs.Witness.SymbolicBounds

set_option autoImplicit false
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate
open LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open Execution Symbolic

def SignalInterpretation (state : SignalState) (assignment : Nat → Fr) (values : Array Nat) : Prop :=
  ∀ (index node : Nat), state.slots[index]?=some (some node) →
    assignment index=model values[node]!

def RootInterpretation (compiled : CompiledGraph) (assignment : Nat → Fr)
    (values : Array Nat) : Prop :=
  ∀ index, assignment index=model values[compiled.signalRoots[index]!]!

theorem signalInterpretation_backwards (before after : SignalState)
    (assignment : Nat → Fr) (values : Array Nat) (extension : SignalExtends before after)
    (interpreted : SignalInterpretation after assignment values) :
    SignalInterpretation before assignment values := by
  intro index node assigned
  exact interpreted index node (extension.2 index node assigned)

theorem signalInterpretation_assigned (state : SignalState) (assignment : Nat → Fr)
    (values : Array Nat) (interpreted : SignalInterpretation state assignment values)
    (index value : Nat) (assigned : Assigned (realize state values) index value) :
    assignment index=model value := by
  have nativeBound := of_getElem?_eq_some assigned
  have bound : index<state.slots.size := by simpa only [realize_size] using nativeBound
  have nativeSlot := assigned_slot (realize state values) index value assigned
  rw [realize_slot state values index bound] at nativeSlot
  cases slot : state.slots[index]! with
  | none => simp [slot] at nativeSlot
  | some node =>
    have equal : values[node]! = value := by simpa only [slot,Option.map_some,Option.some.injEq] using nativeSlot
    have sourceSlot : state.slots[index]?=some (some node) := by
      rw [getElem!_pos state.slots index bound] at slot
      simpa only [Array.getElem?_eq_getElem bound] using congrArg some slot
    rw [interpreted index node sourceSlot,equal]

theorem signalLinear_value (nodes : Array Node) (inputs values : Array Nat)
    (denotes : Denotes nodes inputs values) (compiled : CompiledGraph)
    (assignment : Nat → Fr) (constant : assignment 0=1)
    (interpreted : RootInterpretation compiled assignment values) (index : Nat) :
    linearValue assignment (signalLinear nodes compiled index)=assignment index := by
  cases folded : constantAt nodes compiled.signalRoots[index]! with
  | none => simp only [signalLinear,folded,atomLinear_value]
  | some value =>
    simp only [signalLinear,folded,constantLinear_value assignment constant]
    have actual := constantAt_sound nodes inputs values denotes compiled.signalRoots[index]! value folded
    rw [interpreted index,actual]

theorem empty_system (assignment : Nat → Fr) : SystemSatisfied assignment ({} : LocalSystem) := by
  constructor <;> intro row member <;> simp at member

theorem sumLinear_from (assignment : Nat → Fr) (rows : List Linear) (initial : Linear) :
    linearValue assignment (rows.foldl addLinear initial)=
      linearValue assignment initial+(rows.map (linearValue assignment)).sum := by
  induction rows generalizing initial with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons,ih,linear_add,List.map_cons,List.sum_cons,add_assoc]

theorem sumLinear_value (assignment : Nat → Fr) (rows : List Linear) :
    linearValue assignment (sumLinear rows)=(rows.map (linearValue assignment)).sum := by
  rw [sumLinear,sumLinear_from]
  simp [linearValue,evalSparse]

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.signalInterpretation_backwards
#print axioms TornadoProofs.Witness.Local.signalInterpretation_assigned
#print axioms TornadoProofs.Witness.Local.signalLinear_value
#print axioms TornadoProofs.Witness.Local.empty_system
#print axioms TornadoProofs.Witness.Local.sumLinear_from
#print axioms TornadoProofs.Witness.Local.sumLinear_value
