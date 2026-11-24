import Tornado.Spec.WitnessGadgets
import TornadoProofs.Witness.PrimitiveKind

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Primitive

/-- Agreement with independently supplied values; no execution result occurs
in this read-ready condition. -/
def Reads (state : Assignment) (indices : List Nat) (valueAt : Nat → Nat) : Prop :=
  ∀ index ∈ indices, Assigned state index (valueAt index)

def readInputsFrom (state : Assignment) (indices : List Nat) (acc : Array Nat) :
    Except String (Array Nat) :=
  forIn indices acc fun index values => do
    let value ← state.read index
    pure (.yield (values.push value))

theorem readInputs_construct (state : Assignment) (indices : List Nat)
    (valueAt : Nat → Nat) (reads : Reads state indices valueAt) (acc : Array Nat) :
    readInputsFrom state indices acc = .ok (acc ++ (indices.map valueAt).toArray) := by
  induction indices generalizing acc with
  | nil =>
    change Except.ok acc = Except.ok (acc ++ #[])
    rw [Array.append_empty]
  | cons index rest ih =>
    have read := assigned_read state index (valueAt index) (reads index (by simp))
    have tailReads : Reads state rest valueAt := fun i member => reads i (by simp [member])
    simp only [readInputsFrom, List.forIn_cons, read, bind, Except.bind,
      pure, Except.pure]
    change readInputsFrom state rest (acc.push (valueAt index)) = _
    rw [ih tailReads]
    congr 1
    rw [List.map_cons, List.toArray_cons, Array.append_singleton_assoc]

def outputWrites (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (outputs : Array Nat) : List (Nat × Nat) :=
  (List.range outputs.size).map fun index => (primitive.outputs[index]!, outputs[index]!)

theorem outputLoop_eq (state : Assignment) (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (outputs : Array Nat) :
    (do
      let mut result := state
      for i in [0:outputs.size] do
        result ← result.write primitive.outputs[i]! outputs[i]!
      pure result) = runAssignments state (outputWrites primitive outputs) := by
  change (forIn (Std.Legacy.Range.mk 0 outputs.size 1 (by decide)) state
    (fun i result => do
      let next ← result.write primitive.outputs[i]! outputs[i]!
      pure (ForInStep.yield next)) >>= pure) = _
  rw [bind_pure, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← List.range_eq_range']
  exact (runAssignments_map _ _ _ _).symm

theorem evaluatePrimitive_construct (state : Assignment)
    (primitive : Tornado.Protocol.WitnessVM.Primitive) (kind : Kind)
    (valueAt : Nat → Nat)
    (shape : primitive.shapeValid state.values.size = true)
    (tag : primitive.kind = kind.tag)
    (reads : Reads state primitive.inputs.toList valueAt)
    (admitted : kind.Admitted (primitive.inputs.toList.map valueAt).toArray)
    (count : primitive.outputs.size = kind.count)
    (bounded : Bounded (primitive.inputs.toList.map valueAt).toArray)
    (compatible : CompatibleWrites state
      (outputWrites primitive (kind.values (primitive.inputs.toList.map valueAt).toArray)))
    (consistent : ConsistentWrites
      (outputWrites primitive (kind.values (primitive.inputs.toList.map valueAt).toArray))) :
    ∃ next, evaluatePrimitive state primitive = .ok next ∧ Extends state next ∧
      ∀ index value, (index,value) ∈
        outputWrites primitive (kind.values (primitive.inputs.toList.map valueAt).toArray) →
        Assigned next index value := by
  let inputs := (primitive.inputs.toList.map valueAt).toArray
  have values := kind.construct inputs admitted
  have outputSize : (kind.values inputs).size = primitive.outputs.size :=
    (kind.shape inputs bounded).1.trans count.symm
  rcases runAssignments_construct _ state compatible consistent with
    ⟨next, written, extension, assigned⟩
  refine ⟨next, ?_, extension, assigned⟩
  have read := readInputs_construct state primitive.inputs.toList valueAt reads #[]
  simp only [Array.empty_append] at read
  simp only [evaluatePrimitive, shape, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← Array.forIn_toList]
  change (do
    let inputs ← readInputsFrom state primitive.inputs.toList #[]
    let outputs ← primitiveValues primitive.kind inputs
    if outputs.size != primitive.outputs.size then
      throw s!"Circuit primitive {primitive.name} output count differs from metadata."
    let mut result := state
    for i in [0:outputs.size] do
      result ← result.write primitive.outputs[i]! outputs[i]!
    pure result) = .ok next
  dsimp only [inputs] at values outputSize
  rw [read]
  simp only [bind, Except.bind]
  rw [tag, values]
  have countGuard : ((kind.values inputs).size != primitive.outputs.size) = false := by
    simp only [inputs, outputSize, bne_self_eq_false]
  dsimp only [inputs] at countGuard
  simp only [countGuard,
    Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  simpa only [bind, Except.bind, pure, Except.pure] using
    (outputLoop_eq state primitive (kind.values (primitive.inputs.toList.map valueAt).toArray)).trans written

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.readInputs_construct
#print axioms TornadoProofs.Witness.Execution.outputLoop_eq
#print axioms TornadoProofs.Witness.Execution.evaluatePrimitive_construct
