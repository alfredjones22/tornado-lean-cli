import TornadoProofs.Witness.Expressions
import TornadoProofs.Witness.PrimitiveKind

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Primitive
open Field
open Symbolic
open Tornado.Protocol.WitnessSymbolic

theorem reference_get_value (inputIDs values : Array Nat) (index : Nat)
    (bound : index < inputIDs.size) :
    expressionValue values (inputIDs.map Expression.reference)[index]! =
      (inputIDs.map (values[·]!))[index]! := by
  simp [getElem!_pos, bound, expressionValue]

theorem square_recipe (inputIDs values : Array Nat) (size : inputIDs.size = 1) :
    (primitiveExpressions "Square" inputIDs).map (expressionValue values) =
      square (inputIDs.map (values[·]!)) := by
  simp [primitiveExpressions, square, expressionValue, getElem!_pos, size, mul_eq, 
    LeanCrypto.Groth16.FFT.mul, show LeanCrypto.Groth16.FFT.modulus = q from rfl]

theorem window4_recipe (inputIDs values : Array Nat) (size : inputIDs.size = 2) :
    (primitiveExpressions "Window4" inputIDs).map (expressionValue values) =
      window4 (inputIDs.map (values[·]!)) := by
  simp [primitiveExpressions, window4, expressionValue, getElem!_pos, size, mul_eq, sub_eq, 
    LeanCrypto.Groth16.FFT.mul, LeanCrypto.Groth16.FFT.sub, show LeanCrypto.Groth16.FFT.modulus = q from rfl]

theorem montgomeryAdd_recipe (inputIDs values : Array Nat) (size : inputIDs.size = 4)
    (admitted : Kind.montgomeryAdd.Admitted (inputIDs.map (values[·]!))) :
    (primitiveExpressions "MontgomeryAdd" inputIDs).map (expressionValue values) =
      montgomeryAdd (inputIDs.map (values[·]!)) := by
  have inverse := power_inverse
    (sub (inputIDs.map (values[·]!))[2]! (inputIDs.map (values[·]!))[0]!) admitted
  simp [primitiveExpressions, montgomeryAdd, expressionValue, getElem!_pos, size,
    invValue, mul_eq, sub_eq, LeanCrypto.Groth16.FFT.mul,
    LeanCrypto.Groth16.FFT.sub, show LeanCrypto.Groth16.FFT.modulus = q from rfl] at inverse ⊢
  all_goals simp [inverse]

theorem montgomeryDouble_recipe (inputIDs values : Array Nat) (size : inputIDs.size = 2)
    (admitted : Kind.montgomeryDouble.Admitted (inputIDs.map (values[·]!))) :
    (primitiveExpressions "MontgomeryDouble" inputIDs).map (expressionValue values) =
      montgomeryDouble (inputIDs.map (values[·]!)) := by
  have inverse := power_inverse (mul 2 (inputIDs.map (values[·]!))[1]!) admitted
  simp [primitiveExpressions, montgomeryDouble, expressionValue, getElem!_pos, size,
    invValue, mul_eq, sub_eq, add_eq, LeanCrypto.Groth16.FFT.mul,
    LeanCrypto.Groth16.FFT.sub, LeanCrypto.Groth16.FFT.add,
    show LeanCrypto.Groth16.FFT.modulus = q from rfl] at inverse ⊢
  all_goals simp [inverse]

theorem edwards2Montgomery_recipe (inputIDs values : Array Nat) (size : inputIDs.size = 2)
    (admitted : Kind.edwards2Montgomery.Admitted (inputIDs.map (values[·]!))) :
    (primitiveExpressions "Edwards2Montgomery" inputIDs).map (expressionValue values) =
      edwards2Montgomery (inputIDs.map (values[·]!)) := by
  have inverseY := power_inverse (sub 1 (inputIDs.map (values[·]!))[1]!) admitted.1
  have inverseX := power_inverse ((inputIDs.map (values[·]!))[0]!) admitted.2
  simp [primitiveExpressions, edwards2Montgomery, expressionValue, getElem!_pos, size,
    invValue, mul_eq, sub_eq, add_eq, LeanCrypto.Groth16.FFT.mul,
    LeanCrypto.Groth16.FFT.sub, LeanCrypto.Groth16.FFT.add,
    show LeanCrypto.Groth16.FFT.modulus = q from rfl] at inverseY inverseX ⊢
  all_goals simp [inverseY, inverseX]

theorem montgomery2Edwards_recipe (inputIDs values : Array Nat) (size : inputIDs.size = 2)
    (admitted : Kind.montgomery2Edwards.Admitted (inputIDs.map (values[·]!))) :
    (primitiveExpressions "Montgomery2Edwards" inputIDs).map (expressionValue values) =
      montgomery2Edwards (inputIDs.map (values[·]!)) := by
  have inverseY := power_inverse ((inputIDs.map (values[·]!))[1]!) admitted.1
  have inverseX := power_inverse (add (inputIDs.map (values[·]!))[0]! 1) admitted.2
  simp [primitiveExpressions, montgomery2Edwards, expressionValue, getElem!_pos, size,
    invValue, mul_eq, sub_eq, add_eq, LeanCrypto.Groth16.FFT.mul,
    LeanCrypto.Groth16.FFT.sub, LeanCrypto.Groth16.FFT.add,
    show LeanCrypto.Groth16.FFT.modulus = q from rfl] at inverseY inverseX ⊢
  all_goals simp [inverseY, inverseX]

theorem babyAdd_recipe (inputIDs values : Array Nat) (size : inputIDs.size = 4)
    (admitted : Kind.babyAdd.Admitted (inputIDs.map (values[·]!))) :
    (primitiveExpressions "BabyAdd" inputIDs).map (expressionValue values) =
      babyAdd (inputIDs.map (values[·]!)) := by
  have inversePlus := power_inverse (add 1 (mul 168696 (mul (mul (inputIDs.map (values[·]!))[0]! (inputIDs.map (values[·]!))[3]!) (mul (inputIDs.map (values[·]!))[1]! (inputIDs.map (values[·]!))[2]!)))) admitted.1
  have inverseMinus := power_inverse (sub 1 (mul 168696 (mul (mul (inputIDs.map (values[·]!))[0]! (inputIDs.map (values[·]!))[3]!) (mul (inputIDs.map (values[·]!))[1]! (inputIDs.map (values[·]!))[2]!)))) admitted.2
  simp [primitiveExpressions, babyAdd, expressionValue, getElem!_pos, size,
    invValue, mul_eq, sub_eq, add_eq, LeanCrypto.Groth16.FFT.mul,
    LeanCrypto.Groth16.FFT.sub, LeanCrypto.Groth16.FFT.add,
    show LeanCrypto.Groth16.FFT.modulus = q from rfl] at inversePlus inverseMinus ⊢
  all_goals simp [inversePlus, inverseMinus]

end TornadoProofs.Witness.Primitive
#print axioms TornadoProofs.Witness.Primitive.reference_get_value
#print axioms TornadoProofs.Witness.Primitive.square_recipe
#print axioms TornadoProofs.Witness.Primitive.window4_recipe
#print axioms TornadoProofs.Witness.Primitive.montgomeryAdd_recipe

#print axioms TornadoProofs.Witness.Primitive.montgomeryDouble_recipe

#print axioms TornadoProofs.Witness.Primitive.edwards2Montgomery_recipe

#print axioms TornadoProofs.Witness.Primitive.montgomery2Edwards_recipe

#print axioms TornadoProofs.Witness.Primitive.babyAdd_recipe
