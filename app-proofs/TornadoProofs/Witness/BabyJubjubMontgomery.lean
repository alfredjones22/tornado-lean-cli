import TornadoProofs.Witness.PrimitiveEquations
import LeanCryptoProofs.BabyJubjub.MontgomeryPoint

set_option autoImplicit false
namespace TornadoProofs.Witness.BabyJubjub
open LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BN254Fr

theorem montgomeryAdd_group (i o : Array Nat)
    (first : Montgomery (model i[0]!) (model i[1]!))
    (second : Montgomery (model i[2]!) (model i[3]!))
    (different : model i[0]!≠model i[2]!) (equations : Primitive.MontgomeryAddEquations i o) :
    ∃ equation : Montgomery (model o[1]!) (model o[2]!),
      montgomeryPoint _ _ equation=montgomeryPoint _ _ first+montgomeryPoint _ _ second := by
  rcases equations with ⟨slopeEquation,xEquation,yEquation⟩
  have slope : model o[0]! =montgomerySlope (model i[0]!) (model i[1]!) (model i[2]!) (model i[3]!) :=
    (eq_div_iff (sub_ne_zero.mpr different.symm)).2 slopeEquation
  have x : model o[1]! =montgomeryAddU (model i[0]!) (model i[1]!) (model i[2]!) (model i[3]!) := by
    unfold montgomeryAddU
    rw [←slope]
    linear_combination -xEquation
  have y : model o[2]! =montgomeryAddV (model i[0]!) (model i[1]!) (model i[2]!) (model i[3]!) := by
    unfold montgomeryAddV
    rw [←slope,←x]
    linear_combination -yEquation
  obtain ⟨equation,group⟩ := montgomery_add_construct _ _ _ _ first second different
  have output : Montgomery (model o[1]!) (model o[2]!) := by rw [x,y]; exact equation
  refine ⟨output,?_⟩
  simpa only [x,y] using group

theorem montgomeryDouble_group (i o : Array Nat)
    (first : Montgomery (model i[0]!) (model i[1]!)) (nonzero : model i[1]!≠0)
    (equations : Primitive.MontgomeryDoubleEquations i o) :
    ∃ equation : Montgomery (model o[2]!) (model o[3]!),
      montgomeryPoint _ _ equation=montgomeryPoint _ _ first+montgomeryPoint _ _ first := by
  rcases equations with ⟨squared,slopeEquation,xEquation,yEquation⟩
  rw [squared] at slopeEquation
  have slope : model o[1]! =montgomeryDoubleSlope (model i[0]!) (model i[1]!) := by
    apply (eq_div_iff (mul_ne_zero (by decide +kernel : (2:LeanCrypto.Proofs.BabyJubjub.Field)≠0) nonzero)).2
    simpa only [pow_two] using slopeEquation
  have x : model o[2]! =montgomeryDoubleU (model i[0]!) (model i[1]!) := by
    unfold montgomeryDoubleU
    rw [←slope]
    linear_combination -xEquation
  have y : model o[3]! =montgomeryDoubleV (model i[0]!) (model i[1]!) := by
    unfold montgomeryDoubleV
    rw [←slope,←x]
    linear_combination -yEquation
  obtain ⟨equation,group⟩ := montgomery_double_construct _ _ first nonzero
  have output : Montgomery (model o[2]!) (model o[3]!) := by rw [x,y]; exact equation
  refine ⟨output,?_⟩
  simpa only [x,y] using group

/-- Construct the actual native checked arithmetic and its elliptic-curve
meaning from independent original input coordinates. -/
theorem actual_montgomeryAdd (i : Array Nat)
    (first : Montgomery (model i[0]!) (model i[1]!))
    (second : Montgomery (model i[2]!) (model i[3]!))
    (different : model i[0]!≠model i[2]!) :
    ∃ o, Tornado.Protocol.WitnessVM.primitiveValues "MontgomeryAdd" i=.ok o ∧
      ∃ equation : Montgomery (model o[1]!) (model o[2]!),
        montgomeryPoint _ _ equation=montgomeryPoint _ _ first+montgomeryPoint _ _ second := by
  have difference : model i[2]!-model i[0]!≠0 := sub_ne_zero.mpr different.symm
  refine ⟨Primitive.montgomeryAdd i,Primitive.montgomeryAdd_construct i ?_,?_⟩
  · simpa only [Field.model_sub] using difference
  · exact montgomeryAdd_group i _ first second different (Primitive.montgomeryAdd_equations i difference)

theorem actual_montgomeryDouble (i : Array Nat)
    (first : Montgomery (model i[0]!) (model i[1]!)) (nonzero : model i[1]!≠0) :
    ∃ o, Tornado.Protocol.WitnessVM.primitiveValues "MontgomeryDouble" i=.ok o ∧
      ∃ equation : Montgomery (model o[2]!) (model o[3]!),
        montgomeryPoint _ _ equation=montgomeryPoint _ _ first+montgomeryPoint _ _ first := by
  have denominator := mul_ne_zero (by decide +kernel : (2:LeanCrypto.Proofs.BabyJubjub.Field)≠0) nonzero
  refine ⟨Primitive.montgomeryDouble i,Primitive.montgomeryDouble_construct i ?_,?_⟩
  · simpa only [Field.model_mul,show Field.model 2=(2:LeanCrypto.Proofs.BabyJubjub.Field) from rfl] using denominator
  · exact montgomeryDouble_group i _ first nonzero (Primitive.montgomeryDouble_equations i denominator)

end TornadoProofs.Witness.BabyJubjub
#print axioms TornadoProofs.Witness.BabyJubjub.montgomeryAdd_group
#print axioms TornadoProofs.Witness.BabyJubjub.montgomeryDouble_group
#print axioms TornadoProofs.Witness.BabyJubjub.actual_montgomeryAdd
#print axioms TornadoProofs.Witness.BabyJubjub.actual_montgomeryDouble
