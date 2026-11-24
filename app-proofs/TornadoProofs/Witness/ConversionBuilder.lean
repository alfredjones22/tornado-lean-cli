import TornadoProofs.Witness.MontgomeryBuilder

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr

theorem toMontgomery_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (commitment : Bool)
    (reference : PointRef) (point : Point) (meaning : EdwardsMeaning values reference point)
    (nonzeroX : model values[reference.1]! ≠ 0) (chart : 1-model values[reference.2]! ≠ 0) :
    BuildSpec (Execution.StepsAdmitted values) ((compilerOps resolver commitment).toMontgomery reference)
      (fun result => MontgomeryMeaning values result point) := by
  obtain ⟨curve,equal⟩ := meaning
  let ids := #[reference.1,reference.2]
  let i := ids.map (values[·]!)
  have admitted : Primitive.Kind.edwards2Montgomery.Admitted i := by
    have nativeChart : Field.model (Field.sub 1 values[reference.2]!) ≠ 0 := by
      simpa only [Field.model_sub,show Field.model 1=(1:LeanCrypto.Proofs.BabyJubjub.Field) from rfl] using chart
    simpa [Primitive.Kind.Admitted,i,ids] using And.intro nativeChart nonzeroX
  change BuildSpec _ (do let outputs ← operation resolver "Edwards2Montgomery" ids; pure (outputs[0]!,outputs[1]!)) _
  apply buildSpec_bind _ _ _ _ _ (operation_spec resolver inputs values denotes .edwards2Montgomery ids rfl admitted)
  intro outputs mapped
  apply buildSpec_pure
  have first : Edwards (model i[0]!) (model i[1]!) := by simpa [i,ids] using curve
  have nonzero : model i[0]! ≠ 0 := by simpa [i,ids] using nonzeroX
  have finite : 1-model i[1]! ≠ 0 := by simpa [i,ids] using chart
  obtain ⟨o,built,output,group⟩ := BabyJubjub.actual_edwards2Montgomery i first nonzero finite
  have nativeEqual : o=Primitive.Kind.edwards2Montgomery.values i :=
    Except.ok.inj (built.symm.trans (Primitive.Kind.construct .edwards2Montgomery i admitted))
  subst o
  have x := mapped_index values outputs (Primitive.Kind.edwards2Montgomery.values i) mapped 0 (by change 0<2; omega)
  have y := mapped_index values outputs (Primitive.Kind.edwards2Montgomery.values i) mapped 1 (by change 1<2; omega)
  have outputCurve : Montgomery (model values[outputs[0]!]!) (model values[outputs[1]!]!) := by rw [x,y]; exact output
  refine ⟨outputCurve,?_⟩
  have inputEqual : toMontgomery ⟨model i[0]!,model i[1]!,first⟩=point := by simpa [i,ids] using equal
  simpa only [x,y,inputEqual] using group

theorem toEdwards_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (commitment : Bool)
    (reference : PointRef) (point : Point) (meaning : MontgomeryMeaning values reference point)
    (nonzeroV : model values[reference.2]! ≠ 0) (chart : model values[reference.1]!+1 ≠ 0) :
    BuildSpec (Execution.StepsAdmitted values) ((compilerOps resolver commitment).toEdwards reference)
      (fun result => EdwardsMeaning values result point) := by
  obtain ⟨curve,equal⟩ := meaning
  let ids := #[reference.1,reference.2]
  let i := ids.map (values[·]!)
  have admitted : Primitive.Kind.montgomery2Edwards.Admitted i := by
    have nativeChart : Field.model (Field.add values[reference.1]! 1) ≠ 0 := by
      simpa only [Field.model_add,show Field.model 1=(1:LeanCrypto.Proofs.BabyJubjub.Field) from rfl] using chart
    simpa [Primitive.Kind.Admitted,i,ids] using And.intro nonzeroV nativeChart
  change BuildSpec _ (do let outputs ← operation resolver "Montgomery2Edwards" ids; pure (outputs[0]!,outputs[1]!)) _
  apply buildSpec_bind _ _ _ _ _ (operation_spec resolver inputs values denotes .montgomery2Edwards ids rfl admitted)
  intro outputs mapped
  apply buildSpec_pure
  have first : Montgomery (model i[0]!) (model i[1]!) := by simpa [i,ids] using curve
  have nonzero : model i[1]! ≠ 0 := by simpa [i,ids] using nonzeroV
  have finite : model i[0]!+1 ≠ 0 := by simpa [i,ids] using chart
  obtain ⟨o,built,output,group⟩ := BabyJubjub.actual_montgomery2Edwards i first nonzero finite
  have nativeEqual : o=Primitive.Kind.montgomery2Edwards.values i :=
    Except.ok.inj (built.symm.trans (Primitive.Kind.construct .montgomery2Edwards i admitted))
  subst o
  have x := mapped_index values outputs (Primitive.Kind.montgomery2Edwards.values i) mapped 0 (by change 0<2; omega)
  have y := mapped_index values outputs (Primitive.Kind.montgomery2Edwards.values i) mapped 1 (by change 1<2; omega)
  have outputCurve : Edwards (model values[outputs[0]!]!) (model values[outputs[1]!]!) := by rw [x,y]; exact output
  refine ⟨outputCurve,?_⟩
  have inputEqual : montgomeryPoint _ _ first=point := by simpa [i,ids] using equal
  simpa only [x,y,inputEqual] using group

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.toMontgomery_spec
#print axioms TornadoProofs.Witness.PedersenReference.toEdwards_spec
