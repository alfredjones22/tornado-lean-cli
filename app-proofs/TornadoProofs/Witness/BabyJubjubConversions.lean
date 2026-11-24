import TornadoProofs.Witness.BabyJubjubMontgomery
import LeanCryptoProofs.BabyJubjub.MontgomeryConversion

set_option autoImplicit false
namespace TornadoProofs.Witness.BabyJubjub
open LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BN254Fr

theorem edwards2Montgomery_coordinates (i o : Array Nat)
    (nonzeroX : model i[0]!≠0) (chart : 1-model i[1]!≠0)
    (equations : Primitive.Edwards2MontgomeryEquations i o) :
    model o[0]! = chartU (model i[1]!) ∧ model o[1]! = chartV (model i[0]!) (model i[1]!) := by
  rcases equations with ⟨uEquation,vEquation⟩
  have u : model o[0]! = chartU (model i[1]!) := (eq_div_iff chart).2 uEquation
  refine ⟨u,?_⟩
  apply (eq_div_iff nonzeroX).2
  exact vEquation.trans u

theorem montgomery2Edwards_coordinates (i o : Array Nat)
    (nonzeroV : model i[1]!≠0) (chart : model i[0]!+1≠0)
    (equations : Primitive.Montgomery2EdwardsEquations i o) :
    model o[0]! = fromMontX (model i[0]!) (model i[1]!) ∧ model o[1]! = fromMontY (model i[0]!) :=
  ⟨(eq_div_iff nonzeroV).2 equations.1,(eq_div_iff chart).2 equations.2⟩

theorem actual_edwards2Montgomery (i : Array Nat)
    (first : Edwards (model i[0]!) (model i[1]!))
    (nonzeroX : model i[0]!≠0) (chart : 1-model i[1]!≠0) :
    ∃ o, Tornado.Protocol.WitnessVM.primitiveValues "Edwards2Montgomery" i=.ok o ∧
      ∃ equation : Montgomery (model o[0]!) (model o[1]!),
        montgomeryPoint _ _ equation=toMontgomery ⟨model i[0]!,model i[1]!,first⟩ := by
  have finite : model i[1]!≠1 := (sub_ne_zero.mp chart).symm
  have nativeChart : Field.model (Field.sub 1 i[1]!)≠0 := by
    simpa only [Field.model_sub,show Field.model 1=(1:LeanCrypto.Proofs.BabyJubjub.Field) from rfl] using chart
  let o := Primitive.edwards2Montgomery i
  have returned := Primitive.edwards2Montgomery_construct i nativeChart nonzeroX
  obtain ⟨u,v⟩ := edwards2Montgomery_coordinates i o nonzeroX chart
    (Primitive.edwards2Montgomery_equations i chart nonzeroX)
  have equation : Montgomery (model o[0]!) (model o[1]!) := by
    rw [u,v]
    exact chart_curve _ _ first finite
  refine ⟨o,returned,equation,?_⟩
  rw [toMontgomery,dif_neg finite]
  simp only [montgomeryPoint,WeierstrassCurve.Affine.Point.mk,WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨u,v⟩

theorem actual_montgomery2Edwards (i : Array Nat)
    (first : Montgomery (model i[0]!) (model i[1]!))
    (nonzeroV : model i[1]!≠0) (chart : model i[0]!+1≠0) :
    ∃ o, Tornado.Protocol.WitnessVM.primitiveValues "Montgomery2Edwards" i=.ok o ∧
      ∃ equation : Edwards (model o[0]!) (model o[1]!),
        toMontgomery ⟨model o[0]!,model o[1]!,equation⟩=montgomeryPoint _ _ first := by
  have nativeChart : Field.model (Field.add i[0]! 1)≠0 := by
    simpa only [Field.model_add,show Field.model 1=(1:LeanCrypto.Proofs.BabyJubjub.Field) from rfl] using chart
  let o := Primitive.montgomery2Edwards i
  have returned := Primitive.montgomery2Edwards_construct i nonzeroV nativeChart
  obtain ⟨x,y⟩ := montgomery2Edwards_coordinates i o nonzeroV chart
    (Primitive.montgomery2Edwards_equations i nonzeroV chart)
  have equation : Edwards (model o[0]!) (model o[1]!) := by
    rw [x,y]
    exact fromMont_curve _ _ first nonzeroV chart
  refine ⟨o,returned,equation,?_⟩
  simpa only [x,y] using fromMont_group _ _ first nonzeroV chart

end TornadoProofs.Witness.BabyJubjub
#print axioms TornadoProofs.Witness.BabyJubjub.edwards2Montgomery_coordinates
#print axioms TornadoProofs.Witness.BabyJubjub.montgomery2Edwards_coordinates
#print axioms TornadoProofs.Witness.BabyJubjub.actual_edwards2Montgomery
#print axioms TornadoProofs.Witness.BabyJubjub.actual_montgomery2Edwards
