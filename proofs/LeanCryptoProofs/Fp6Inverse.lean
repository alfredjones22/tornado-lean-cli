import LeanCryptoProofs.Fp6Model
open Lean Elab Term Meta
elab "actualFp6InverseCandidate" : term =>
  mkConstWithFreshMVarLevels
    (mkPrivateNameCore `LeanCrypto.BN254.PairingField `LeanCrypto.BN254.PairingField.Fp6.inverseCandidate)

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Fp6
open LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField

def cofactor (value : Fp6) : Fp6 :=
  ⟨(value.c0.mul value.c0).sub (nonresidue.mul (value.c1.mul value.c2)),
   (nonresidue.mul (value.c2.mul value.c2)).sub (value.c0.mul value.c1),
   (value.c1.mul value.c1).sub (value.c0.mul value.c2)⟩

def denominator (value : Fp6) : Fp2 :=
  (value.c0.mul (cofactor value).c0).add (nonresidue.mul
    ((value.c2.mul (cofactor value).c1).add (value.c1.mul (cofactor value).c2)))

def embed (value : Fp2) : Fp6 := ⟨value, Fp2.zero, Fp2.zero⟩

@[simp]
theorem model_embed (value : Fp2) :
    model (embed value) = algebraMap Base Field (BN254Fp2.model value) := by
  simp [model_formula, embed]

theorem native_cofactor_product (value : Fp6) :
    value.mul (cofactor value) = embed (denominator value) := by
  apply native_ext
  · apply BN254Fp2.model_injective
    simp only [Fp6.mul, cofactor, embed, denominator, BN254Fp2.model_add, BN254Fp2.model_mul, BN254Fp2.model_sub]
    ring
  · apply BN254Fp2.model_injective
    simp only [Fp6.mul, cofactor, embed, BN254Fp2.model_add, BN254Fp2.model_mul, BN254Fp2.model_sub, BN254Fp2.model_zero]
    ring
  · apply BN254Fp2.model_injective
    simp only [Fp6.mul, cofactor, embed, BN254Fp2.model_add, BN254Fp2.model_mul, BN254Fp2.model_sub, BN254Fp2.model_zero]
    ring

theorem cofactor_coordinates_zero {F : Type} [_root_.Field F] (xi a b c : F)
    (noCube : ∀ value : F, value ^ 3 ≠ xi)
    (first : a * a - xi * (b * c) = 0)
    (second : xi * (c * c) - a * b = 0)
    (third : b * b - a * c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have eq0 := sub_eq_zero.mp first
  have eq1 := sub_eq_zero.mp second
  have eq2 := sub_eq_zero.mp third
  by_cases lastZero : c = 0
  · have middleZero : b = 0 := by
      rw [lastZero, mul_zero] at eq2
      exact mul_self_eq_zero.mp eq2
    have firstZero : a = 0 := by
      rw [middleZero, zero_mul, mul_zero] at eq0
      exact mul_self_eq_zero.mp eq0
    exact ⟨firstZero, middleZero, lastZero⟩
  · apply False.elim
    apply noCube (b / c)
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 3 lastZero)).mpr
    calc
      b ^ 3 = (b * b) * b := by ring
      _ = a * b * c := by rw [eq2]; ring
      _ = xi * c ^ 3 := by rw [← eq1]; ring

theorem cofactor_nonzero (value : Fp6) (nonzero : model value ≠ 0) :
    model (cofactor value) ≠ 0 := by
  intro zero
  have nativeZero : cofactor value = Fp6.zero := model_injective (zero.trans model_zero.symm)
  have zero0 := congrArg (fun t : Fp6 => BN254Fp2.model t.c0) nativeZero
  have zero1 := congrArg (fun t : Fp6 => BN254Fp2.model t.c1) nativeZero
  have zero2 := congrArg (fun t : Fp6 => BN254Fp2.model t.c2) nativeZero
  simp only [cofactor, Fp6.zero, BN254Fp2.model_sub, BN254Fp2.model_mul, BN254Fp2.model_zero] at zero0 zero1 zero2
  obtain ⟨first, middle, last⟩ := cofactor_coordinates_zero _ _ _ _
    BN254Fp2.nonresidue_not_cube zero0 zero1 zero2
  apply nonzero
  simp [model_formula, first, middle, last]

theorem denominator_nonzero (value : Fp6) (nonzero : model value ≠ 0) :
    BN254Fp2.model (denominator value) ≠ 0 := by
  intro zero
  have product := congrArg model (native_cofactor_product value)
  rw [model_mul, model_embed, zero, map_zero] at product
  exact (mul_ne_zero nonzero (cofactor_nonzero value nonzero)) product

def scale (value : Fp6) (factor : Fp2) : Fp6 :=
  ⟨value.c0.mul factor, value.c1.mul factor, value.c2.mul factor⟩

theorem model_scale (value : Fp6) (factor : Fp2) :
    model (scale value factor) = model value * algebraMap Base Field (BN254Fp2.model factor) := by
  simp only [model_formula, scale, BN254Fp2.model_mul, map_mul]
  ring

abbrev nativeInverseCandidate (value : Fp6) : Except String Fp6 := actualFp6InverseCandidate value

/-- Actual cofactor inversion and its product guard construct the inverse
for every independently nonzero input; no successful native call is assumed. -/
theorem inverse_complete (value : Fp6) (nonzero : model value ≠ 0) :
    value.inverse = .ok (encode ((model value)⁻¹)) := by
  let inverse := BN254Fp2.encode ((BN254Fp2.model (denominator value))⁻¹)
  let candidate := scale (cofactor value) inverse
  have denNonzero := denominator_nonzero value nonzero
  have denInverse : (denominator value).inverse = .ok inverse :=
    BN254Fp2.inverse_complete _ denNonzero
  have product : model value * model candidate = 1 := by
    rw [show model candidate = model (cofactor value) *
      algebraMap Base Field ((BN254Fp2.model (denominator value))⁻¹) by
        simpa only [candidate, inverse, BN254Fp2.model_encode] using model_scale (cofactor value) inverse]
    rw [← mul_assoc, ← model_mul, native_cofactor_product, model_embed, ← map_mul,
      mul_inv_cancel₀ denNonzero, map_one]
  have candidateMeaning : model candidate = (model value)⁻¹ := by
    apply mul_left_cancel₀ nonzero
    rw [product, mul_inv_cancel₀ nonzero]
  have candidateEqual : candidate = encode ((model value)⁻¹) :=
    model_injective (by simpa using candidateMeaning)
  have notZero : (value == Fp6.zero) = false := by
    apply Bool.eq_false_iff.mpr
    intro zero
    exact nonzero ((model_beq _ _).1 zero |>.trans model_zero)
  have candidateSource : nativeInverseCandidate value = .ok candidate := by
    change (do
      if value == Fp6.zero then throw "BN254 Fp6 zero has no inverse."
      let inv ← (denominator value).inverse
      return scale (cofactor value) inv) = .ok candidate
    simp only [notZero, Bool.false_eq_true, ↓reduceIte, denInverse, bind, Except.bind,
      pure, Except.pure]
    rfl
  have guard : (value.mul candidate == Fp6.one) = true :=
    (model_beq _ _).2 (by simpa using product)
  change (match nativeInverseCandidate value with
    | .error error => Except.error error
    | .ok result => if value.mul result == Fp6.one then Except.ok result
      else Except.error "BN254 Fp6 inverse check failed.") = _
  simp only [candidateSource]
  rw [guard]
  exact congrArg Except.ok candidateEqual

theorem inverse_total (value : Fp6) :
    value.inverse = if model value = 0 then .error "BN254 Fp6 zero has no inverse."
      else .ok (encode ((model value)⁻¹)) := by
  classical
  by_cases zero : model value = 0
  · have nativeZero : value = Fp6.zero := model_injective (zero.trans model_zero.symm)
    subst value
    simp only [model_zero, ↓reduceIte]
    rfl
  · rw [if_neg zero]
    exact inverse_complete value zero

end LeanCrypto.Proofs.BN254Fp6

#print axioms LeanCrypto.Proofs.BN254Fp6.model_embed
#print axioms LeanCrypto.Proofs.BN254Fp6.native_cofactor_product
#print axioms LeanCrypto.Proofs.BN254Fp6.cofactor_coordinates_zero
#print axioms LeanCrypto.Proofs.BN254Fp6.cofactor_nonzero
#print axioms LeanCrypto.Proofs.BN254Fp6.denominator_nonzero
#print axioms LeanCrypto.Proofs.BN254Fp6.model_scale
#print axioms LeanCrypto.Proofs.BN254Fp6.inverse_complete
#print axioms LeanCrypto.Proofs.BN254Fp6.inverse_total
