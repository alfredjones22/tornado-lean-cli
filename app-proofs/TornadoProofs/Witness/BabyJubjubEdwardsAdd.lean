import TornadoProofs.Witness.BabyJubjubConversions
import LeanCryptoProofs.BabyJubjub.GroupLaw

set_option autoImplicit false
namespace TornadoProofs.Witness.BabyJubjub
open LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BN254Fr

theorem babyAdd_coordinates (i o : Array Nat)
    (first : Edwards (model i[0]!) (model i[1]!))
    (second : Edwards (model i[2]!) (model i[3]!))
    (equations : Primitive.BabyAddEquations i o) :
    model o[4]! = edwardsAddX (model i[0]!) (model i[1]!) (model i[2]!) (model i[3]!) ∧
    model o[5]! = edwardsAddY (model i[0]!) (model i[1]!) (model i[2]!) (model i[3]!) := by
  rcases equations with ⟨beta,gamma,delta,tau,xEquation,yEquation⟩
  dsimp only [Field.model] at beta gamma delta tau xEquation yEquation
  have denominators := LeanCrypto.Proofs.BabyJubjubComplete.babyjub_complete_denominators
    _ _ _ _ first second
  have plus : 1+168696*model o[3]! =1+168696*model i[0]!*model i[2]!*model i[1]!*model i[3]! := by
    rw [tau,beta,gamma]
    ring
  have minus : 1-168696*model o[3]! =1-168696*model i[0]!*model i[2]!*model i[1]!*model i[3]! := by
    rw [tau,beta,gamma]
    ring
  constructor
  · unfold edwardsAddX
    apply (eq_div_iff denominators.1).2
    simpa only [plus,beta,gamma] using xEquation
  · unfold edwardsAddY
    apply (eq_div_iff denominators.2).2
    rw [minus,delta,beta,gamma] at yEquation
    linear_combination yEquation

/-- Complete Edwards denominators construct the actual checked VM helper,
including segment sums that may be the group identity. -/
theorem actual_babyAdd (i : Array Nat)
    (first : Edwards (model i[0]!) (model i[1]!))
    (second : Edwards (model i[2]!) (model i[3]!)) :
    ∃ o, Tornado.Protocol.WitnessVM.primitiveValues "BabyAdd" i=.ok o ∧
      ∃ equation : Edwards (model o[4]!) (model o[5]!),
        toMontgomery ⟨model o[4]!,model o[5]!,equation⟩=
          toMontgomery ⟨model i[0]!,model i[1]!,first⟩+toMontgomery ⟨model i[2]!,model i[3]!,second⟩ := by
  have denominators := LeanCrypto.Proofs.BabyJubjubComplete.babyjub_complete_denominators
    _ _ _ _ first second
  have plus : (1:LeanCrypto.Proofs.BabyJubjub.Field)+168696*((model i[0]!*model i[3]!)*(model i[1]!*model i[2]!))≠0 := by
    convert denominators.1 using 1; ring
  have minus : (1:LeanCrypto.Proofs.BabyJubjub.Field)-168696*((model i[0]!*model i[3]!)*(model i[1]!*model i[2]!))≠0 := by
    convert denominators.2 using 1; ring
  have nativePlus : Field.model (Field.add 1 (Field.mul 168696 (Field.mul (Field.mul i[0]! i[3]!) (Field.mul i[1]! i[2]!))))≠0 := by
    simpa only [Field.model_add,Field.model_mul,show Field.model 1=(1:LeanCrypto.Proofs.BabyJubjub.Field) from rfl,
      show Field.model 168696=(168696:LeanCrypto.Proofs.BabyJubjub.Field) from rfl] using plus
  have nativeMinus : Field.model (Field.sub 1 (Field.mul 168696 (Field.mul (Field.mul i[0]! i[3]!) (Field.mul i[1]! i[2]!))))≠0 := by
    simpa only [Field.model_sub,Field.model_mul,show Field.model 1=(1:LeanCrypto.Proofs.BabyJubjub.Field) from rfl,
      show Field.model 168696=(168696:LeanCrypto.Proofs.BabyJubjub.Field) from rfl] using minus
  let o := Primitive.babyAdd i
  have returned := Primitive.babyAdd_construct i nativePlus nativeMinus
  obtain ⟨x,y⟩ := babyAdd_coordinates i o first second (Primitive.babyAdd_equations i plus minus)
  have equation : Edwards (model o[4]!) (model o[5]!) := by
    rw [x,y]
    exact edwards_add_curve _ _ _ _ first second
  refine ⟨o,returned,equation,?_⟩
  simpa only [EPoint.add,x,y] using toMontgomery_add ⟨_,_,first⟩ ⟨_,_,second⟩

end TornadoProofs.Witness.BabyJubjub
#print axioms TornadoProofs.Witness.BabyJubjub.babyAdd_coordinates
#print axioms TornadoProofs.Witness.BabyJubjub.actual_babyAdd
