import TornadoProofs.Witness.SignalRealization
import TornadoProofs.Witness.OrderedArrays

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Tornado.Protocol.WitnessSymbolic

theorem read_assigned_of_success (state : Assignment) (index value : Nat)
    (returned : state.read index = .ok value) : Assigned state index value := by
  by_cases out : index >= state.values.size
  · simp [Assignment.read,out,bind,Except.bind] at returned
  have bound : index<state.values.size := by omega
  cases slot : state.values[index]! with
  | none => simp [Assignment.read,out,slot,bind,Except.bind,pure,Except.pure] at returned
  | some prior =>
    have equal : prior=value := by
      simpa [Assignment.read,out,slot,bind,Except.bind,pure,Except.pure] using returned
    subst prior
    unfold Assigned
    rw [getElem!_pos state.values index bound] at slot
    simpa only [Array.getElem?_eq_getElem bound] using congrArg some slot

theorem readInputs_ordered (state : SignalState) (values : Array Nat)
    (indices roots : List Nat)
    (ordered : List.Forall₂ (fun index root => state.read index=.ok root) indices roots)
    (acc : Array Nat) :
    readInputsFrom (realize state values) indices acc =
      .ok (acc++(roots.map (values[·]!)).toArray) := by
  induction ordered generalizing acc with
  | nil =>
    change Except.ok acc=Except.ok (acc++#[])
    rw [Array.append_empty]
  | @cons index root indices roots found tail ih =>
    have actual := signalRead_realize state values index root found
    simp only [readInputsFrom,List.forIn_cons,actual,bind,Except.bind,pure,Except.pure]
    change readInputsFrom (realize state values) indices (acc.push values[root]!) = _
    rw [ih]
    congr 1
    rw [List.map_cons,List.toArray_cons,Array.append_singleton_assoc]

theorem readInputs_realize (state : SignalState) (values indices roots : Array Nat)
    (compiled : indices.mapM state.read = .ok roots) :
    readInputsFrom (realize state values) indices.toList #[] = .ok (roots.map (values[·]!)) := by
  have ordered := arrayMapM_ordered state.read indices roots compiled
  simpa only [Array.empty_append,← List.map_toArray,Array.toArray_toList] using
    readInputs_ordered state values indices.toList roots.toList ordered #[]

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.read_assigned_of_success
#print axioms TornadoProofs.Witness.Execution.readInputs_ordered
#print axioms TornadoProofs.Witness.Execution.readInputs_realize
