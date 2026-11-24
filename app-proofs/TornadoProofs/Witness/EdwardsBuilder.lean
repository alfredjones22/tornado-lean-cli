import TornadoProofs.Witness.ConversionBuilder

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr

theorem babyAdded_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (firstRef secondRef : PointRef) (firstPoint secondPoint : Point)
    (firstMeaning : EdwardsMeaning values firstRef firstPoint)
    (secondMeaning : EdwardsMeaning values secondRef secondPoint) :
    BuildSpec (Execution.StepsAdmitted values) (babyAdded resolver firstRef secondRef)
      (fun result => EdwardsMeaning values result (firstPoint+secondPoint)) := by
  obtain ⟨first,equalFirst⟩ := firstMeaning
  obtain ⟨second,equalSecond⟩ := secondMeaning
  let ids := #[firstRef.1,firstRef.2,secondRef.1,secondRef.2]
  let i := ids.map (values[·]!)
  have firstCurve : Edwards (model i[0]!) (model i[1]!) := by simpa [i,ids] using first
  have secondCurve : Edwards (model i[2]!) (model i[3]!) := by simpa [i,ids] using second
  have denominators := LeanCrypto.Proofs.BabyJubjubComplete.babyjub_complete_denominators _ _ _ _ firstCurve secondCurve
  have admitted : Primitive.Kind.babyAdd.Admitted i := by
    change Field.model (Field.add 1 (Field.mul 168696 (Field.mul (Field.mul i[0]! i[3]!) (Field.mul i[1]! i[2]!)))) ≠ 0 ∧
      Field.model (Field.sub 1 (Field.mul 168696 (Field.mul (Field.mul i[0]! i[3]!) (Field.mul i[1]! i[2]!)))) ≠ 0
    simp only [Field.model_add,Field.model_sub,Field.model_mul,
      show Field.model 1=(1:LeanCrypto.Proofs.BabyJubjub.Field) from rfl,
      show Field.model 168696=(168696:LeanCrypto.Proofs.BabyJubjub.Field) from rfl]
    constructor
    · convert denominators.1 using 1; ring
    · convert denominators.2 using 1; ring
  unfold babyAdded
  apply buildSpec_bind _ _ _ _ _ (operation_spec resolver inputs values denotes .babyAdd ids rfl admitted)
  intro outputs mapped
  apply buildSpec_pure
  obtain ⟨o,built,output,group⟩ := BabyJubjub.actual_babyAdd i firstCurve secondCurve
  have nativeEqual : o=Primitive.Kind.babyAdd.values i :=
    Except.ok.inj (built.symm.trans (Primitive.Kind.construct .babyAdd i admitted))
  subst o
  have x := mapped_index values outputs (Primitive.Kind.babyAdd.values i) mapped 4 (by change 4<6; omega)
  have y := mapped_index values outputs (Primitive.Kind.babyAdd.values i) mapped 5 (by change 5<6; omega)
  have outputCurve : Edwards (model values[outputs[4]!]!) (model values[outputs[5]!]!) := by rw [x,y]; exact output
  refine ⟨outputCurve,?_⟩
  have firstEqual : toMontgomery ⟨model i[0]!,model i[1]!,firstCurve⟩=firstPoint := by simpa [i,ids] using equalFirst
  have secondEqual : toMontgomery ⟨model i[2]!,model i[3]!,secondCurve⟩=secondPoint := by simpa [i,ids] using equalSecond
  simpa only [x,y,firstEqual,secondEqual] using group

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.babyAdded_spec
