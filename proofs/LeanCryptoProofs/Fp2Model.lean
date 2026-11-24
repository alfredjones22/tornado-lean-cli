import LeanCryptoProofs.CertifiedFields
import LeanCrypto.BN254.G2
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.Ring

/-! Independent quadratic-field interpretation of the actual native Fp2
arithmetic. The no-root and inverse constructions are derived from the
certified base prime; no successful final native inverse check is assumed. -/
set_option autoImplicit false

namespace LeanCrypto.Proofs.BN254Fp2

open LeanCrypto.BN254.G1 LeanCrypto.BN254.G2
open LeanCrypto.Proofs.BN254Fp

theorem base_mod_four : P % 4 = 3 := by decide +kernel

theorem no_square_neg_one (value : ZMod P) : value ^ 2 ≠ -1 := by
  intro square
  have nonzero : value ≠ 0 := by
    intro zero
    rw [zero, zero_pow (by decide)] at square
    exact (neg_ne_zero.mpr one_ne_zero) square.symm
  have fermat := model_fermat value nonzero
  have exponent : P - 1 = 2 * ((P - 1) / 2) := by decide +kernel
  have odd : Odd ((P - 1) / 2) := ⟨(P - 3) / 4, by decide +kernel⟩
  rw [exponent, pow_mul, square, odd.neg_one_pow] at fermat
  exact (by decide +kernel : (-1 : ZMod P) ≠ 1) fermat

instance noQuadraticRoot : Fact (∀ value : ZMod P, value ^ 2 ≠ -1 + 0 * value) :=
  ⟨fun value => by simpa using no_square_neg_one value⟩

abbrev Field := QuadraticAlgebra (ZMod P) (-1) 0

def model (value : Fp2) : Field :=
  ⟨BN254Fp.model value.c0, BN254Fp.model value.c1⟩

def encode (value : Field) : Fp2 :=
  ⟨BN254Fp.encode value.re, BN254Fp.encode value.im⟩

theorem native_ext {left right : Fp2} (real : left.c0 = right.c0) (imaginary : left.c1 = right.c1) :
    left = right := by
  cases left
  cases right
  cases real
  cases imaginary
  rfl

theorem model_injective : Function.Injective model := by
  intro left right equal
  apply native_ext
  · exact BN254Fp.model_injective (congrArg QuadraticAlgebra.re equal)
  · exact BN254Fp.model_injective (congrArg QuadraticAlgebra.im equal)

@[simp]
theorem encode_model (value : Fp2) : encode (model value) = value := by
  apply native_ext <;> simp [encode, model]

@[simp]
theorem model_encode (value : Field) : model (encode value) = value := by
  ext <;> simp [encode, model]

@[simp]
theorem model_zero : model Fp2.zero = 0 := by ext <;> simp [model, Fp2.zero]
@[simp]
theorem model_one : model Fp2.one = 1 := by
  apply QuadraticAlgebra.ext <;> change _ = _ <;> simp [model, Fp2.one]
  all_goals rfl

theorem model_ofNats (real imaginary : Nat) :
    model (Fp2.ofNats real imaginary) = ⟨(real : ZMod P), (imaginary : ZMod P)⟩ := by
  ext <;> simp [model, Fp2.ofNats]

@[simp]
theorem model_ofNat (value : Nat) : model (Fp2.ofNats value 0) = (value : Field) := by
  ext <;> simp [model, Fp2.ofNats, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]

@[simp]
theorem model_add (left right : Fp2) : model (left.add right) = model left + model right := by
  ext <;> simp [model, Fp2.add]

@[simp]
theorem model_neg (value : Fp2) : model value.neg = -model value := by
  ext <;> simp [model, Fp2.neg]

@[simp]
theorem model_sub (left right : Fp2) : model (left.sub right) = model left - model right := by
  simp [Fp2.sub, sub_eq_add_neg]

@[simp]
theorem model_mul (left right : Fp2) : model (left.mul right) = model left * model right := by
  ext <;> simp [model, Fp2.mul, sub_eq_add_neg]

theorem model_beq (left right : Fp2) : (left == right) = true ↔ model left = model right := by
  change ((left.c0 == right.c0) && (left.c1 == right.c1)) = true ↔ _
  rw [Bool.and_eq_true, BN254Fp.model_beq, BN254Fp.model_beq]
  constructor
  · rintro ⟨real, imaginary⟩
    ext <;> assumption
  · intro equal
    exact ⟨congrArg QuadraticAlgebra.re equal, congrArg QuadraticAlgebra.im equal⟩

theorem model_denominator (value : Fp2) :
    BN254Fp.model ((value.c0.mul value.c0).add (value.c1.mul value.c1)) =
      QuadraticAlgebra.norm (model value) := by
  simp [model, QuadraticAlgebra.norm_def]

theorem denominator_nonzero (value : Fp2) (nonzero : model value ≠ 0) :
    BN254Fp.model ((value.c0.mul value.c0).add (value.c1.mul value.c1)) ≠ 0 := by
  rw [model_denominator]
  exact fun zero => nonzero (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp zero)

/-- Every nonzero native Fp2 value constructs its mathematical field inverse
with the actual denominator/cofactor implementation, including its final
native product guard. No successful-return premise occurs. -/
theorem inverse_complete (value : Fp2) (nonzero : model value ≠ 0) :
    value.inverse = .ok (encode ((model value)⁻¹)) := by
  let denominator := (value.c0.mul value.c0).add (value.c1.mul value.c1)
  let inverse := BN254Fp.encode ((BN254Fp.model denominator)⁻¹)
  let candidate : Fp2 := ⟨value.c0.mul inverse, value.c1.neg.mul inverse⟩
  have denNonzero := denominator_nonzero value nonzero
  have denInverse : denominator.inverse = .ok inverse := BN254Fp.inverse_complete denominator denNonzero
  have representedDenominator : BN254Fp.model denominator =
      BN254Fp.model value.c0 * BN254Fp.model value.c0 +
      BN254Fp.model value.c1 * BN254Fp.model value.c1 := by simp [denominator]
  have reducedNonzero : BN254Fp.model value.c0 * BN254Fp.model value.c0 +
      BN254Fp.model value.c1 * BN254Fp.model value.c1 ≠ 0 := by
    rw [← representedDenominator]
    exact denNonzero
  have product : model value * model candidate = 1 := by
    apply QuadraticAlgebra.ext
    · simp [model, candidate, inverse, representedDenominator, QuadraticAlgebra.re_one]
      ring_nf
      rw [← add_mul, mul_inv_cancel₀ (show BN254Fp.model value.c0 ^ 2 +
        BN254Fp.model value.c1 ^ 2 ≠ 0 by simpa [pow_two] using reducedNonzero)]
    · simp [model, candidate, inverse, representedDenominator, QuadraticAlgebra.im_one]
      ring
  have representedInverse : model candidate = (model value)⁻¹ := by
    apply mul_left_cancel₀ nonzero
    rw [product, mul_inv_cancel₀ nonzero]
  have equalCandidate : candidate = encode ((model value)⁻¹) :=
    model_injective (by simpa using representedInverse)
  have guard : (value.mul candidate == Fp2.one) = true := by
    apply (model_beq _ _).2
    simpa using product
  simp only [Fp2.inverse, show (value.c0.mul value.c0).add (value.c1.mul value.c1) = denominator from rfl,
    denInverse, bind, Except.bind, pure, Except.pure]
  change (if value.mul candidate != Fp2.one then (Except.error _ : Except String Fp2)
    else .ok candidate) = .ok (encode ((model value)⁻¹))
  simp only [bne, guard, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact congrArg Except.ok equalCandidate

theorem inverse_total (value : Fp2) :
    value.inverse = if model value = 0 then .error "BN254 Fp zero has no inverse."
      else .ok (encode ((model value)⁻¹)) := by
  by_cases zero : model value = 0
  · have nativeZero : value = Fp2.zero := model_injective (by simpa using zero)
    subst value
    simp only [model_zero, ↓reduceIte]
    rfl
  · rw [if_neg zero]
    exact inverse_complete value zero

theorem affine_onCurve_iff (point : LeanCrypto.BN254.G2.Affine) : point.onCurve = true ↔
    model point.y ^ 2 = model point.x ^ 3 + model twistB := by
  rw [LeanCrypto.BN254.G2.Affine.onCurve, model_beq]
  simp only [model_mul, model_add]
  simp only [pow_succ, pow_zero, one_mul]

noncomputable instance modelFintype : Fintype Field :=
  Fintype.ofEquiv (ZMod P × ZMod P) (QuadraticAlgebra.equivProd (-1) 0).symm

theorem model_card : Fintype.card Field = P ^ 2 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd (-1) 0), Fintype.card_prod, ZMod.card]
  exact (pow_two P).symm

end LeanCrypto.Proofs.BN254Fp2

#print axioms LeanCrypto.Proofs.BN254Fp2.base_mod_four
#print axioms LeanCrypto.Proofs.BN254Fp2.no_square_neg_one
#print axioms LeanCrypto.Proofs.BN254Fp2.native_ext
#print axioms LeanCrypto.Proofs.BN254Fp2.model_injective
#print axioms LeanCrypto.Proofs.BN254Fp2.encode_model
#print axioms LeanCrypto.Proofs.BN254Fp2.model_encode
#print axioms LeanCrypto.Proofs.BN254Fp2.model_zero
#print axioms LeanCrypto.Proofs.BN254Fp2.model_one
#print axioms LeanCrypto.Proofs.BN254Fp2.model_ofNats
#print axioms LeanCrypto.Proofs.BN254Fp2.model_ofNat
#print axioms LeanCrypto.Proofs.BN254Fp2.model_add
#print axioms LeanCrypto.Proofs.BN254Fp2.model_neg
#print axioms LeanCrypto.Proofs.BN254Fp2.model_sub
#print axioms LeanCrypto.Proofs.BN254Fp2.model_mul
#print axioms LeanCrypto.Proofs.BN254Fp2.model_beq
#print axioms LeanCrypto.Proofs.BN254Fp2.model_denominator
#print axioms LeanCrypto.Proofs.BN254Fp2.denominator_nonzero
#print axioms LeanCrypto.Proofs.BN254Fp2.inverse_complete
#print axioms LeanCrypto.Proofs.BN254Fp2.inverse_total
#print axioms LeanCrypto.Proofs.BN254Fp2.affine_onCurve_iff
#print axioms LeanCrypto.Proofs.BN254Fp2.model_card
