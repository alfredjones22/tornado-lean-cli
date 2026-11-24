import TornadoProofs.Witness.MetadataState

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic

def unwrapSignal : Option Nat → Except String Nat
  | none => .error "Public witness DAG does not assign every internal signal."
  | some node => .ok node

theorem slots_complete (state : SignalState) (roots : Array Nat)
    (returned : state.slots.mapM unwrapSignal=.ok roots) : state.slots=roots.map some := by
  have mapped := arrayMapM_value unwrapSignal state.slots roots id some
    (fun slot root found => by cases slot <;> simp [unwrapSignal] at found ⊢; subst root; rfl) returned
  simpa only [Array.map_id] using mapped.symm

theorem complete_nodeFits (state : SignalState) (compiled : CompiledGraph)
    (complete : state.slots=compiled.signalRoots.map some) : NodeFits compiled state := by
  intro index node assigned
  have bound : index<compiled.signalRoots.size := by
    have b := of_getElem?_eq_some assigned
    simpa only [complete,Array.size_map] using b
  rw [complete,Array.getElem?_eq_getElem (by simpa using bound)] at assigned
  simpa only [Array.getElem_map,Option.some.injEq,← getElem!_pos compiled.signalRoots index bound] using assigned

theorem complete_realize_read (state : SignalState) (roots values : Array Nat)
    (complete : state.slots=roots.map some) (index : Nat) (bound : index<roots.size) :
    (realize state values).read index=.ok values[roots[index]!]! := by
  apply signalRead_realize state values index roots[index]!
  have size : state.slots.size=roots.size := by simp [complete]
  simp [SignalState.read,Nat.not_le_of_lt bound,complete,getElem!_pos,bound,bind,Except.bind,pure,Except.pure]

theorem forIn_unit_construct {A : Type} (items : List A)
    (step : A → PUnit.{1} → Except String (ForInStep PUnit.{1}))
    (valid : ∀ item∈items,step item PUnit.unit=.ok (.yield PUnit.unit)) :
    forIn items PUnit.unit step=.ok PUnit.unit := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    rw [List.forIn_cons,valid head (by simp)]
    exact ih (fun item member => valid item (by simp [member]))

theorem forIn_read_push {A : Type} (items : List A) (read : A → Except String Nat)
    (meaning : A → Nat) (valid : ∀ item∈items,read item=.ok (meaning item)) (initial : Array Nat) :
    forIn items initial (fun item current => do
      let value ← read item
      pure (ForInStep.yield (current.push value)))=.ok (initial++(items.map meaning).toArray) := by
  induction items generalizing initial with
  | nil => simp [pure,Except.pure]
  | cons head tail ih =>
    rw [List.forIn_cons]
    simp only [valid head (by simp),bind,Except.bind,pure,Except.pure]
    change (forIn tail (initial.push (meaning head)) (fun item current => do
      let value ← read item
      pure (ForInStep.yield (current.push value)))) = _
    rw [ih (fun item member => valid item (by simp [member]))]
    congr 1
    rw [List.map_cons,List.toArray_cons]
    simp only [Array.push_eq_append,Array.append_assoc]

theorem toWitness_complete (graph : SelectedGraph) (state : SignalState) (roots values : Array Nat)
    (layout : graph.layoutValid=true) (complete : state.slots=roots.map some)
    (size : roots.size=graph.nSignals) (variableBound : graph.nVars≤graph.nSignals) :
    (realize state values).toWitness graph =
      .ok ((List.range graph.nVars).map (fun index => values[roots[index]!]!)).toArray := by
  have actualSize : (realize state values).values.size=graph.nSignals := by simp [realize,complete,size]
  let checkStep (index : Nat) (_ : PUnit.{1}) : Except String (ForInStep PUnit.{1}) :=
    if ((realize state values).values[index]!).isNone then
      .error s!"Internal circuit signal {index} has not been computed."
    else .ok (.yield PUnit.unit)
  have check (index : Nat) (member : index∈List.range graph.nSignals) :
      checkStep index PUnit.unit=.ok (.yield PUnit.unit) := by
    have bound : index<roots.size := by simpa only [size] using List.mem_range.mp member
    simp [checkStep,realize,complete,getElem!_pos,bound]
  have checked := forIn_unit_construct (List.range graph.nSignals) checkStep check
  have read : ∀ index∈List.range graph.nVars,
      (realize state values).read index=.ok values[roots[index]!]! := by
    intro index member
    apply complete_realize_read state roots values complete index
    rw [size]
    exact Nat.lt_of_lt_of_le (List.mem_range.mp member) variableBound
  have collected := forIn_read_push (List.range graph.nVars) (realize state values).read
    (fun index => values[roots[index]!]!) read #[]
  unfold Assignment.toWitness
  simp only [layout,Bool.not_true,actualSize,bne_self_eq_false,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  rw [forIn_range_zero,forIn_range_zero]
  simp only [pure,Except.pure,bind,Except.bind]
  change (do
    forIn (List.range graph.nSignals) PUnit.unit checkStep
    let result ← forIn (List.range graph.nVars) #[] (fun index current => do
      let value ← (realize state values).read index
      pure (ForInStep.yield (current.push value)))
    pure result) = _
  rw [checked]
  change ((forIn (List.range graph.nVars) #[] (fun index current => do
    let value ← (realize state values).read index
    pure (ForInStep.yield (current.push value)))) >>= pure) = _
  rw [bind_pure]
  simpa only [Array.empty_append] using collected

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.slots_complete
#print axioms TornadoProofs.Witness.Execution.complete_nodeFits
#print axioms TornadoProofs.Witness.Execution.complete_realize_read
#print axioms TornadoProofs.Witness.Execution.forIn_unit_construct
#print axioms TornadoProofs.Witness.Execution.forIn_read_push
#print axioms TornadoProofs.Witness.Execution.toWitness_complete

