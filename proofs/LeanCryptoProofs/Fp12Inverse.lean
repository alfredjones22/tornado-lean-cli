import LeanCryptoProofs.Fp12Model
open Lean Elab Term Meta
elab "actualFp12InverseCandidate" : term =>
  mkConstWithFreshMVarLevels
    (mkPrivateNameCore `LeanCrypto.BN254.PairingField `LeanCrypto.BN254.PairingField.Fp12.inverseCandidate)

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Fp12
open LeanCrypto.BN254.PairingField

def denominator (value : Fp12) : Fp6 :=
  (value.c0.mul value.c0).sub ((value.c1.mul value.c1).mulByV)

theorem model_denominator (value : Fp12) :
    BN254Fp6.model (denominator value) = QuadraticAlgebra.norm (model value) := by
  simp [denominator, model, QuadraticAlgebra.norm_def, mul_comm, mul_left_comm]

theorem denominator_nonzero (value : Fp12) (nonzero : model value ≠ 0) :
    BN254Fp6.model (denominator value) ≠ 0 := by
  rw [model_denominator]
  exact mt QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp nonzero

abbrev nativeInverseCandidate (value : Fp12) : Except String Fp12 := actualFp12InverseCandidate value

theorem inverse_complete (value : Fp12) (nonzero : model value ≠ 0) :
    value.inverse = .ok (encode ((model value)⁻¹)) := by
  let inverse := BN254Fp6.encode ((BN254Fp6.model (denominator value))⁻¹)
  let candidate : Fp12 := ⟨value.c0.mul inverse, value.c1.neg.mul inverse⟩
  have denInverse : (denominator value).inverse = .ok inverse :=
    BN254Fp6.inverse_complete _ (denominator_nonzero value nonzero)
  have candidateMeaning : model candidate = (model value)⁻¹ := by
    change model candidate = (QuadraticAlgebra.norm (model value))⁻¹ • star (model value)
    rw [← model_denominator]
    ext <;> simp [model, candidate, inverse, smul_eq_mul, mul_comm]
  have candidateEqual : candidate = encode ((model value)⁻¹) :=
    model_injective (by simpa using candidateMeaning)
  have notZero : (value == Fp12.zero) = false := by
    apply Bool.eq_false_iff.mpr
    intro zero
    exact nonzero ((model_beq _ _).1 zero |>.trans model_zero)
  have candidateSource : nativeInverseCandidate value = .ok candidate := by
    change (do
      if value == Fp12.zero then throw "BN254 Fp12 zero has no inverse."
      let inv ← (denominator value).inverse
      return (⟨value.c0.mul inv, value.c1.neg.mul inv⟩ : Fp12)) = .ok candidate
    simp only [notZero, Bool.false_eq_true, ↓reduceIte, denInverse, bind, Except.bind,
      pure, Except.pure]
    rfl
  have guard : (value.mul candidate == Fp12.one) = true := by
    apply (model_beq _ _).2
    rw [model_mul, model_one, candidateMeaning, mul_inv_cancel₀ nonzero]
  change (match nativeInverseCandidate value with
    | .error error => Except.error error
    | .ok result => if value.mul result == Fp12.one then Except.ok result
      else Except.error "BN254 Fp12 inverse check failed.") = _
  simp only [candidateSource]
  rw [guard]
  exact congrArg Except.ok candidateEqual

theorem inverse_total (value : Fp12) :
    value.inverse = if model value = 0 then .error "BN254 Fp12 zero has no inverse."
      else .ok (encode ((model value)⁻¹)) := by
  classical
  by_cases zero : model value = 0
  · have nativeZero : value = Fp12.zero := model_injective (zero.trans model_zero.symm)
    subst value
    simp only [model_zero, ↓reduceIte]
    rfl
  · rw [if_neg zero]
    exact inverse_complete value zero

end LeanCrypto.Proofs.BN254Fp12
#print axioms LeanCrypto.Proofs.BN254Fp12.model_denominator
#print axioms LeanCrypto.Proofs.BN254Fp12.denominator_nonzero
#print axioms LeanCrypto.Proofs.BN254Fp12.inverse_complete
#print axioms LeanCrypto.Proofs.BN254Fp12.inverse_total
