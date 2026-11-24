import TornadoProofs.Witness.PrimitiveSimulation
import TornadoProofs.Witness.SignalRows
import TornadoProofs.Witness.FeistelSupport

set_option autoImplicit false
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr
open Execution Primitive Symbolic

theorem primitive_stage_parts (resolver : Resolver) (state after : SignalState)
    (p : Tornado.Protocol.WitnessVM.Primitive)
    (compiled : compilePrimitiveStage resolver state p=.ok after) :
    p.shapeValid state.slots.size=true ∧ ∃ roots outputs,
      p.inputs.mapM state.read=.ok roots ∧
      compilePrimitive resolver p.kind roots=.ok outputs ∧
      state.writeMany p.outputs outputs=.ok after := by
  by_cases shape : p.shapeValid state.slots.size=true
  · refine ⟨shape,?_⟩
    simp only [compilePrimitiveStage,shape,Bool.not_true,Bool.false_eq_true,↓reduceIte] at compiled
    obtain ⟨roots,read,remaining⟩ := bind_success (p.inputs.mapM state.read) _ after compiled
    obtain ⟨outputs,built,written⟩ := bind_success (compilePrimitive resolver p.kind roots) _ after remaining
    exact ⟨roots,outputs,read,built,written⟩
  · have invalid := Bool.eq_false_iff.mpr shape
    simp [compilePrimitiveStage,invalid,bind,Except.bind] at compiled

/-- Successful public writes yield ordered semantic input/output values in
any interpretation of the resulting state, including permitted equal-value
aliases. This constructs native writes; no final witness acceptance is used. -/
theorem primitive_stage_meaning (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values)
    (canonical : ∀ (index : Nat), values[index]! < Tornado.Protocol.Groth16R1CS.scalarPrime)
    (state after : SignalState) (p : Tornado.Protocol.WitnessVM.Primitive) (kind : Kind)
    (tag : p.kind=kind.tag)
    (admitted : ∀ roots, p.inputs.mapM state.read=.ok roots → kind.Admitted (roots.map (values[·]!)))
    (compiled : compilePrimitiveStage resolver state p=.ok after)
    (aliases : AliasesValid after values) (assignment : Nat → Fr)
    (interpreted : SignalInterpretation after assignment values) :
    ∃ i, kind.Admitted i ∧ p.inputs.size=kind.inputCount ∧ p.outputs.size=kind.count ∧
      (∀ j, j<p.inputs.size → assignment p.inputs[j]! = model i[j]!) ∧
      (∀ j, j<p.outputs.size → assignment p.outputs[j]! = model (kind.values i)[j]!) := by
  obtain ⟨shape,roots,outputs,read,built,written⟩ := primitive_stage_parts resolver state after p compiled
  have dimensions := primitive_shape_dimensions p kind state.slots.size tag shape
  have rootSize := arrayMapM_size state.read p.inputs roots read
  have rootCount : roots.size=kind.inputCount := rootSize.trans dimensions.1
  have outputValues := compilePrimitive_values resolver inputs values denotes kind roots outputs
    rootCount (admitted roots read) (by simpa only [tag] using built)
  have count : p.outputs.size=outputs.size := by
    by_contra different
    simp [SignalState.writeMany,different,bind,Except.bind] at written
  have constructed := (signalWriteMany_construct state after values p.outputs outputs written canonical aliases).2
  have writes : runAssignments (realize state values) (outputWrites p (outputs.map (values[·]!)))=
      .ok (realize after values) := by
    rw [←outputLoop_eq]
    simpa only [Array.size_map] using constructed
  have post := runAssignments_success _ _ _ writes
  have inputValues : roots.map (fun node => model values[node]!)=p.inputs.map assignment :=
    arrayMapM_value state.read p.inputs roots assignment (fun node => model values[node]!)
      (by
        intro index node returned
        have original := read_assigned_of_success (realize state values) index values[node]!
          (signalRead_realize state values index node returned)
        exact (signalInterpretation_assigned after assignment values interpreted _ _
          (post.1.2 _ _ original)).symm) read
  refine ⟨roots.map (values[·]!),admitted roots read,dimensions.1,dimensions.2,?_,?_⟩
  · intro j bound
    have equal := congrArg (fun a : Array Fr => a[j]!) inputValues
    have rootBound : j<roots.size := by omega
    simpa only [getElem!_pos (roots.map (fun node => model values[node]!)) j (by simpa only [Array.size_map] using rootBound),
      getElem!_pos (p.inputs.map assignment) j (by simpa only [Array.size_map] using bound),Array.getElem_map,
      getElem!_pos roots j rootBound,getElem!_pos p.inputs j bound,
      getElem!_pos (roots.map (values[·]!)) j (by simpa only [Array.size_map] using rootBound)] using equal.symm
  · intro j bound
    have outputBound : j<(outputs.map (values[·]!)).size := by simpa only [Array.size_map] using (show j<outputs.size by omega)
    have assigned := post.2 p.outputs[j]! (outputs.map (values[·]!))[j]!
      (List.mem_map.mpr ⟨j,List.mem_range.mpr outputBound,rfl⟩)
    have known := signalInterpretation_assigned after assignment values interpreted _ _ assigned
    simpa only [outputValues] using known

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.primitive_stage_parts
#print axioms TornadoProofs.Witness.Local.primitive_stage_meaning
