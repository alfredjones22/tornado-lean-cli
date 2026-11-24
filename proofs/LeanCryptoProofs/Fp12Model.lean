import LeanCryptoProofs.Fp6Exponent
import LeanCryptoProofs.Fp6Inverse
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Fp12
open LeanCrypto.BN254.PairingField

abbrev Base := BN254Fp6.Field
instance noQuadraticRoot : Fact (∀ value : Base, value ^ 2 ≠ BN254Fp6.model Fp6.v + 0 * value) :=
  ⟨fun value => by simpa using BN254Fp6.v_not_square value⟩
abbrev Field := QuadraticAlgebra Base (BN254Fp6.model Fp6.v) 0

def model (value : Fp12) : Field := ⟨BN254Fp6.model value.c0, BN254Fp6.model value.c1⟩
def encode (value : Field) : Fp12 := ⟨BN254Fp6.encode value.re, BN254Fp6.encode value.im⟩

theorem native_ext {left right : Fp12} (real : left.c0 = right.c0) (imaginary : left.c1 = right.c1) :
    left = right := by cases left; cases right; cases real; cases imaginary; rfl

theorem model_injective : Function.Injective model := by
  intro left right equal
  apply native_ext
  · exact BN254Fp6.model_injective (congrArg QuadraticAlgebra.re equal)
  · exact BN254Fp6.model_injective (congrArg QuadraticAlgebra.im equal)

@[simp]
theorem encode_model (value : Fp12) : encode (model value) = value := by
  apply native_ext <;> simp [encode, model]
@[simp]
theorem model_encode (value : Field) : model (encode value) = value := by
  ext <;> simp [encode, model]
@[simp]
theorem model_zero : model Fp12.zero = 0 := by ext <;> simp [model, Fp12.zero]
@[simp]
theorem model_one : model Fp12.one = 1 := by
  apply QuadraticAlgebra.ext <;> change _ = _ <;> simp [model, Fp12.one]
  all_goals rfl
@[simp]
theorem model_w : model Fp12.w = QuadraticAlgebra.omega := by
  ext <;> simp [model, Fp12.w]

@[simp]
theorem model_add (left right : Fp12) : model (left.add right) = model left + model right := by
  ext <;> simp [model, Fp12.add]
@[simp]
theorem model_neg (value : Fp12) : model value.neg = -model value := by
  ext <;> simp [model, Fp12.neg]
@[simp]
theorem model_sub (left right : Fp12) : model (left.sub right) = model left - model right := by
  simp [Fp12.sub, sub_eq_add_neg]
@[simp]
theorem model_mul (left right : Fp12) : model (left.mul right) = model left * model right := by
  ext <;> simp [model, Fp12.mul, mul_comm, mul_assoc]
@[simp]
theorem model_square (value : Fp12) : model value.square = model value ^ 2 := by
  simp [Fp12.square, pow_two]
@[simp]
theorem model_conjugate (value : Fp12) : model value.conjugate = star (model value) := by
  ext <;> simp [model, Fp12.conjugate]

theorem model_beq (left right : Fp12) : (left == right) = true ↔ model left = model right := by
  change ((left.c0 == right.c0) && (left.c1 == right.c1)) = true ↔ _
  rw [Bool.and_eq_true, BN254Fp6.model_beq, BN254Fp6.model_beq]
  constructor
  · rintro ⟨real, imaginary⟩
    ext <;> assumption
  · intro equal
    exact ⟨congrArg QuadraticAlgebra.re equal, congrArg QuadraticAlgebra.im equal⟩

end LeanCrypto.Proofs.BN254Fp12

#print axioms LeanCrypto.Proofs.BN254Fp12.native_ext
#print axioms LeanCrypto.Proofs.BN254Fp12.model_injective
#print axioms LeanCrypto.Proofs.BN254Fp12.encode_model
#print axioms LeanCrypto.Proofs.BN254Fp12.model_encode
#print axioms LeanCrypto.Proofs.BN254Fp12.model_zero
#print axioms LeanCrypto.Proofs.BN254Fp12.model_one
#print axioms LeanCrypto.Proofs.BN254Fp12.model_w
#print axioms LeanCrypto.Proofs.BN254Fp12.model_add
#print axioms LeanCrypto.Proofs.BN254Fp12.model_neg
#print axioms LeanCrypto.Proofs.BN254Fp12.model_sub
#print axioms LeanCrypto.Proofs.BN254Fp12.model_mul
#print axioms LeanCrypto.Proofs.BN254Fp12.model_square
#print axioms LeanCrypto.Proofs.BN254Fp12.model_conjugate
#print axioms LeanCrypto.Proofs.BN254Fp12.model_beq
