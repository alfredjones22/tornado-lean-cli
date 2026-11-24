import TornadoProofs.Witness.OperationFacts

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr

theorem doubled_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (reference : PointRef) (point : Point)
    (meaning : MontgomeryMeaning values reference point) (nonzero : model values[reference.2]! ≠ 0) :
    BuildSpec (Execution.StepsAdmitted values) (doubled resolver reference)
      (fun result => MontgomeryMeaning values result (point+point)) := by
  obtain ⟨curve,equal⟩ := meaning
  let ids := #[reference.1,reference.2]
  let i := ids.map (values[·]!)
  have admitted : Primitive.Kind.montgomeryDouble.Admitted i := by
    have denominator : Field.model (Field.mul 2 values[reference.2]!) ≠ 0 := by
      rw [Field.model_mul]
      exact mul_ne_zero (by decide +kernel : Field.model 2 ≠ 0) nonzero
    simpa [Primitive.Kind.Admitted,i,ids] using denominator
  unfold doubled
  apply buildSpec_bind _ _ _ _ _ (operation_spec resolver inputs values denotes .montgomeryDouble ids rfl admitted)
  intro outputs mapped
  apply buildSpec_pure
  have first : Montgomery (model i[0]!) (model i[1]!) := by simpa [i,ids] using curve
  have denom : model i[1]! ≠ 0 := by simpa [i,ids] using nonzero
  obtain ⟨output,group⟩ := BabyJubjub.montgomeryDouble_group i (Primitive.montgomeryDouble i) first denom
    (Primitive.montgomeryDouble_equations i (mul_ne_zero (by decide +kernel) denom))
  have x := mapped_index values outputs (Primitive.montgomeryDouble i) (by simpa only [Primitive.Kind.values] using mapped) 2 (by change 2<4; omega)
  have y := mapped_index values outputs (Primitive.montgomeryDouble i) (by simpa only [Primitive.Kind.values] using mapped) 3 (by change 3<4; omega)
  have outputCurve : Montgomery (model values[outputs[2]!]!) (model values[outputs[3]!]!) := by rw [x,y]; exact output
  refine ⟨outputCurve,?_⟩
  have inputEqual : montgomeryPoint _ _ first=point := by simpa [i,ids] using equal
  simpa only [x,y,inputEqual] using group

theorem added_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (firstRef secondRef : PointRef) (firstPoint secondPoint : Point)
    (firstMeaning : MontgomeryMeaning values firstRef firstPoint)
    (secondMeaning : MontgomeryMeaning values secondRef secondPoint)
    (different : model values[firstRef.1]! ≠ model values[secondRef.1]!) :
    BuildSpec (Execution.StepsAdmitted values) (added resolver firstRef secondRef)
      (fun result => MontgomeryMeaning values result (firstPoint+secondPoint)) := by
  obtain ⟨first,equalFirst⟩ := firstMeaning
  obtain ⟨second,equalSecond⟩ := secondMeaning
  let ids := #[firstRef.1,firstRef.2,secondRef.1,secondRef.2]
  let i := ids.map (values[·]!)
  have admitted : Primitive.Kind.montgomeryAdd.Admitted i := by
    have denominator : Field.model (Field.sub values[secondRef.1]! values[firstRef.1]!) ≠ 0 := by
      rw [Field.model_sub]
      exact sub_ne_zero.mpr different.symm
    simpa [Primitive.Kind.Admitted,i,ids] using denominator
  unfold added
  apply buildSpec_bind _ _ _ _ _ (operation_spec resolver inputs values denotes .montgomeryAdd ids rfl admitted)
  intro outputs mapped
  apply buildSpec_pure
  have firstCurve : Montgomery (model i[0]!) (model i[1]!) := by simpa [i,ids] using first
  have secondCurve : Montgomery (model i[2]!) (model i[3]!) := by simpa [i,ids] using second
  have diff : model i[0]! ≠ model i[2]! := by simpa [i,ids] using different
  obtain ⟨output,group⟩ := BabyJubjub.montgomeryAdd_group i (Primitive.montgomeryAdd i) firstCurve secondCurve diff
    (Primitive.montgomeryAdd_equations i (sub_ne_zero.mpr diff.symm))
  have x := mapped_index values outputs (Primitive.montgomeryAdd i) (by simpa only [Primitive.Kind.values] using mapped) 1 (by change 1<3; omega)
  have y := mapped_index values outputs (Primitive.montgomeryAdd i) (by simpa only [Primitive.Kind.values] using mapped) 2 (by change 2<3; omega)
  have outputCurve : Montgomery (model values[outputs[1]!]!) (model values[outputs[2]!]!) := by rw [x,y]; exact output
  refine ⟨outputCurve,?_⟩
  have firstEqual : montgomeryPoint _ _ firstCurve=firstPoint := by simpa [i,ids] using equalFirst
  have secondEqual : montgomeryPoint _ _ secondCurve=secondPoint := by simpa [i,ids] using equalSecond
  simpa only [x,y,firstEqual,secondEqual] using group

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.doubled_spec
#print axioms TornadoProofs.Witness.PedersenReference.added_spec
