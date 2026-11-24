import Tornado.Protocol.PedersenSchedule
import TornadoProofs.Witness.CanonicalSource

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.PedersenSchedule

/-- Source arithmetic conditions on the independently generated schedule,
with original ordered DAG input roots for every operation. -/
def StepsAdmitted (values : Array Nat) (steps : Array Footprint) : Prop :=
  ∀ step∈steps,∀ kind : Primitive.Kind,step.kind=kind.tag → kind.Admitted (step.inputs.map (values[·]!))

theorem signalRoot_meaning (compiled : CompiledGraph) (index node : Nat)
    (returned : signalRoot compiled index=.ok node) : node=compiled.signalRoots[index]! := by
  cases lookup : compiled.signalRoots[index]? with
  | none => simp [signalRoot,lookup] at returned
  | some prior =>
    have equal : prior=node := by simpa only [signalRoot,lookup,Except.ok.injEq] using returned
    subst prior
    have bound := of_getElem?_eq_some lookup
    rw [getElem!_pos compiled.signalRoots index bound]
    exact Option.some.inj (lookup.symm.trans (Array.getElem?_eq_getElem bound))

theorem actualFootprint_inputs (compiled : CompiledGraph) (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (footprint : Footprint) (returned : actualFootprint compiled primitive=.ok footprint) :
    footprint.kind=primitive.kind ∧ footprint.inputs=primitive.inputs.map (compiled.signalRoots[·]!) := by
  by_cases valid : primitive.shapeValid compiled.signalRoots.size=true
  · simp only [actualFootprint,valid,Bool.not_true,Bool.false_eq_true,↓reduceIte,pure_bind] at returned
    obtain ⟨inputs,read,returned⟩ := bind_success _ _ footprint returned
    obtain ⟨outputs,_,returned⟩ := bind_success _ _ footprint returned
    have equal : Footprint.mk primitive.kind inputs outputs=footprint := Except.ok.inj returned
    rw [←equal]
    refine ⟨rfl,?_⟩
    have mapped := arrayMapM_value (signalRoot compiled) primitive.inputs inputs (compiled.signalRoots[·]!) id
      (fun index node found => signalRoot_meaning compiled index node found) read
    simpa only [Array.map_id] using mapped
  · simp [actualFootprint,Bool.eq_false_of_not_eq_true valid,bind,Except.bind] at returned

def pointStepEffect (compiled : CompiledGraph) (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (current : Array Footprint) : Except String (ForInStep (Array Footprint)) :=
  if primitive.kind != "Square" then do
    let footprint ← actualFootprint compiled primitive
    pure (.yield (current.push footprint))
  else pure (.yield current)

theorem actualPointSteps_source (compiled : CompiledGraph) (graph : SelectedGraph) :
    actualPointSteps compiled graph=forIn graph.primitives.toList #[] (pointStepEffect compiled) := by
  unfold actualPointSteps
  simp only [pure_bind]
  change ((forIn graph.primitives #[] (pointStepEffect compiled)) >>= pure)=_
  rw [bind_pure,←Array.forIn_toList]

theorem pointSteps_forIn_members (compiled : CompiledGraph)
    (items : List Tornado.Protocol.WitnessVM.Primitive) (initial result : Array Footprint)
    (returned : forIn items initial (pointStepEffect compiled)=.ok result) :
    (∀ footprint∈initial,footprint∈result) ∧
      ∀ primitive∈items,primitive.kind≠"Square" → ∃ footprint,
        actualFootprint compiled primitive=.ok footprint ∧ footprint∈result := by
  induction items generalizing initial with
  | nil =>
    have equal : initial=result := Except.ok.inj returned
    subst result
    exact ⟨fun _ member => member,by simp⟩
  | cons primitive tail ih =>
    by_cases nonSquare : primitive.kind≠"Square"
    · have checked : (primitive.kind != "Square")=true := by simp [nonSquare]
      simp only [List.forIn_cons,pointStepEffect,checked,↓reduceIte,bind_assoc,pure_bind] at returned
      obtain ⟨footprint,built,returned⟩ := bind_success (actualFootprint compiled primitive) _ result returned
      have after := ih (initial.push footprint) returned
      refine ⟨fun fp member => after.1 fp (Array.mem_push.mpr (Or.inl member)),?_⟩
      intro item member different
      rcases List.mem_cons.mp member with equal | member
      · subst item
        exact ⟨footprint,built,after.1 footprint (Array.mem_push_self)⟩
      · exact after.2 item member different
    · have equal : primitive.kind="Square" := Classical.byContradiction nonSquare
      simp only [List.forIn_cons,pointStepEffect,equal,bne_self_eq_false,Bool.false_eq_true,
        ↓reduceIte,pure_bind] at returned
      have after := ih initial returned
      refine ⟨after.1,?_⟩
      intro item member different
      rcases List.mem_cons.mp member with same | member
      · subst item
        exact False.elim (different equal)
      · exact after.2 item member different

theorem actualPointSteps_member (compiled : CompiledGraph) (graph : SelectedGraph) (actual : Array Footprint)
    (observed : actualPointSteps compiled graph=.ok actual)
    (primitive : Tornado.Protocol.WitnessVM.Primitive) (member : primitive∈graph.primitives)
    (nonSquare : primitive.kind≠"Square") :
    ∃ footprint,actualFootprint compiled primitive=.ok footprint ∧ footprint∈actual := by
  rw [actualPointSteps_source] at observed
  exact (pointSteps_forIn_members compiled graph.primitives.toList #[] actual observed).2 primitive
    (Array.mem_toList_iff.mpr member) nonSquare

theorem intended_steps_admit_primitives (compiled : CompiledGraph) (graph : SelectedGraph)
    (expected actual : Array Footprint) (values : Array Nat)
    (observed : actualPointSteps compiled graph=.ok actual)
    (intended : ∀ footprint∈actual,footprint∈expected) (admitted : StepsAdmitted values expected) :
    ∀ primitive∈graph.primitives,PrimitiveSourceAdmitted compiled values primitive := by
  intro primitive member kind tag
  by_cases square : kind=.square
  · subst kind
    trivial
  have nonSquare : primitive.kind≠"Square" := by
    intro equal
    have different : kind.tag≠"Square" := by cases kind <;> simp_all [Primitive.Kind.tag]
    exact different (tag.symm.trans equal)
  obtain ⟨footprint,built,belongs⟩ := actualPointSteps_member compiled graph actual observed primitive member nonSquare
  obtain ⟨sameKind,sameInputs⟩ := actualFootprint_inputs compiled primitive footprint built
  have source := admitted footprint (intended footprint belongs) kind (sameKind.trans tag)
  simpa only [sameInputs,Array.map_map,Function.comp_def] using source

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.signalRoot_meaning
#print axioms TornadoProofs.Witness.Execution.actualFootprint_inputs
#print axioms TornadoProofs.Witness.Execution.actualPointSteps_source
#print axioms TornadoProofs.Witness.Execution.pointSteps_forIn_members
#print axioms TornadoProofs.Witness.Execution.actualPointSteps_member
#print axioms TornadoProofs.Witness.Execution.intended_steps_admit_primitives
