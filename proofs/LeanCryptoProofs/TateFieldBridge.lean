import LeanCryptoProofs.Fp12Inverse
import LeanCryptoProofs.Fp12Exponent
import LeanCrypto.BN254.TatePairing

open Lean Elab Term Meta
elab "actualTateDivide" : term =>
  mkConstWithFreshMVarLevels
    (mkPrivateNameCore `LeanCrypto.BN254.TatePairing `LeanCrypto.BN254.TatePairing.divide)

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G1 LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField
open LeanCrypto.BN254.TatePairing BN254Fp12

def finalExponent : Nat := (basePrime ^ 12 - 1) / scalarPrime

theorem final_exponent_product : finalExponent * scalarPrime = basePrime ^ 12 - 1 := by
  decide +kernel

theorem final_power_nonzero (value : Fp12) (nonzero : model value ≠ 0) :
    model (value.pow finalExponent) ≠ 0 := by
  rw [model_pow]
  exact pow_ne_zero _ nonzero

theorem final_power_order (value : Fp12) (nonzero : model value ≠ 0) :
    ((value.pow finalExponent).pow scalarPrime == Fp12.one) = true := by
  apply (model_beq _ _).2
  rw [model_pow, model_pow, model_one, ← pow_mul, final_exponent_product]
  exact field_fermat _ nonzero

abbrev nativeDivide (numerator denominator : Fp12) : Except String Fp12 :=
  actualTateDivide numerator denominator

/-- Every native division with independently nonzero denominator constructs
the independent field quotient, including all actual inverse guards. -/
theorem divide_construct (numerator denominator : Fp12) (nonzero : model denominator ≠ 0) :
    nativeDivide numerator denominator = .ok (encode (model numerator / model denominator)) := by
  have inverse := inverse_complete denominator nonzero
  have guard : (denominator == Fp12.zero) = false := by
    apply Bool.eq_false_iff.mpr
    intro zero
    exact nonzero ((model_beq _ _).1 zero |>.trans model_zero)
  change (do
    if denominator == Fp12.zero then throw "BN254 pairing line denominator is zero."
    return numerator.mul (← denominator.inverse)) = _
  simp only [guard, Bool.false_eq_true, ↓reduceIte, inverse, bind, Except.bind,
    pure, Except.pure]
  apply congrArg Except.ok
  apply model_injective
  simp [div_eq_mul_inv]

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.final_exponent_product
#print axioms LeanCrypto.Proofs.BN254Tate.final_power_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.final_power_order
#print axioms LeanCrypto.Proofs.BN254Tate.divide_construct
