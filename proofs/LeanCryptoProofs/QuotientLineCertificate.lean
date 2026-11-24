import LeanCryptoProofs.GeneratorTraceChecker

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing BN254Fp12

theorem checked_nonzero (value : Fp12) (checked : (value == Fp12.zero) = false) : model value ≠ 0 := by
  intro zero
  have equal := (model_beq value Fp12.zero).2 (zero.trans model_zero.symm)
  rw [checked] at equal
  contradiction

theorem divide_product_certificate (numerator denominator quotient : Fp12)
    (nonzero : (denominator == Fp12.zero) = false)
    (product : (quotient.mul denominator == numerator) = true) :
    nativeDivide numerator denominator = .ok quotient := by
  have den := checked_nonzero denominator nonzero
  have multiplication := (model_beq _ _).1 product
  rw [model_mul] at multiplication
  have quotientMeaning : model quotient = model numerator / model denominator := (eq_div_iff den).2 multiplication
  have encoded : encode (model numerator / model denominator) = quotient := by
    apply model_injective
    rw [model_encode, ← quotientMeaning]
  rw [← encoded]
  exact divide_construct numerator denominator den

structure LineHint where
  slope : Fp12
  factor : Fp12
  result : Option Point

def finiteLineSum (r s : Point) (slope : Fp12) : Point :=
  let x := (slope.square.sub r.x).sub s.x
  ⟨x, (slope.mul (r.x.sub x)).sub r.y⟩

def slopeNumerator (r s : Point) : Fp12 :=
  if r.x == s.x && r.y == s.y then r.x.square.mul (embedFp (LeanCrypto.BN254.G1.Fp.ofNat 3)) else s.y.sub r.y
def slopeDenominator (r s : Point) : Fp12 :=
  if r.x == s.x && r.y == s.y then r.y.mul (embedFp (LeanCrypto.BN254.G1.Fp.ofNat 2)) else s.x.sub r.x
def factorNumerator (r evaluation : Point) (slope : Fp12) : Fp12 :=
  (evaluation.y.sub r.y).sub (slope.mul (evaluation.x.sub r.x))

def finiteLineChecks (r s evaluation : Point) (hint : LineHint) : Prop :=
  (slopeDenominator r s == Fp12.zero) = false ∧
  (hint.slope.mul (slopeDenominator r s) == slopeNumerator r s) = true ∧
  (evaluation.x.sub (finiteLineSum r s hint.slope).x == Fp12.zero) = false ∧
  (hint.factor.mul (evaluation.x.sub (finiteLineSum r s hint.slope).x) == factorNumerator r evaluation hint.slope) = true ∧
  (hint.factor == Fp12.zero) = false ∧
  optionalPointEqual hint.result (some (finiteLineSum r s hint.slope)) = true

instance (r s evaluation : Point) (hint : LineHint) : Decidable (finiteLineChecks r s evaluation hint) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def lineHintCheck (r s evaluation : Point) (hint : LineHint) : Bool :=
  if r.x == s.x && r.y == s.y.neg then
    decide ((hint.factor == evaluation.x.sub r.x) = true ∧ (hint.factor == Fp12.zero) = false ∧
      optionalPointEqual hint.result none = true)
  else decide (finiteLineChecks r s evaluation hint)

theorem lineHintCheck_sound (r s evaluation : Point) (hint : LineHint)
    (checked : lineHintCheck r s evaluation hint = true) :
    nativeLineAndSum r s evaluation = .ok (hint.factor, hint.result) := by
  by_cases vertical : (r.x == s.x && r.y == s.y.neg) = true
  · have fields : (hint.factor == evaluation.x.sub r.x) = true ∧ (hint.factor == Fp12.zero) = false ∧
        optionalPointEqual hint.result none = true :=
      of_decide_eq_true (by simpa only [lineHintCheck, if_pos vertical] using checked)
    have factorEq := model_injective ((model_beq _ _).1 fields.1)
    have pointEq := optionalPointEqual_sound hint.result none fields.2.2
    rw [nativeLineAndSum_source]
    simp only [vertical, ↓reduceIte, ← factorEq, fields.2.1, Bool.false_eq_true, bind, Except.bind,
      pure, Except.pure]
    rw [pointEq]
  · have fields : finiteLineChecks r s evaluation hint :=
      of_decide_eq_true (by simpa only [lineHintCheck, if_neg vertical] using checked)
    obtain ⟨slopeNonzero, slopeProduct, factorNonzero, factorProduct, valueNonzero, resultChecked⟩ := fields
    have slope := divide_product_certificate (slopeNumerator r s) (slopeDenominator r s) hint.slope slopeNonzero slopeProduct
    have quotient := divide_product_certificate (factorNumerator r evaluation hint.slope)
      (evaluation.x.sub (finiteLineSum r s hint.slope).x) hint.factor factorNonzero factorProduct
    have pointEq := optionalPointEqual_sound hint.result _ resultChecked
    have finish : (do
        let value ← nativeDivide (factorNumerator r evaluation hint.slope)
          (evaluation.x.sub (finiteLineSum r s hint.slope).x)
        if value == Fp12.zero then throw "BN254 pairing line evaluated to zero."
        return (value, some (finiteLineSum r s hint.slope))) = .ok (hint.factor, hint.result) := by
      rw [quotient]
      simp only [bind, Except.bind, valueNonzero, Bool.false_eq_true, ↓reduceIte]
      rw [pointEq]
      rfl
    by_cases tangent : (r.x == s.x && r.y == s.y) = true
    · have selected : nativeDivide (r.x.square.mul (embedFp (LeanCrypto.BN254.G1.Fp.ofNat 3)))
          (r.y.mul (embedFp (LeanCrypto.BN254.G1.Fp.ofNat 2))) = .ok hint.slope := by
        simpa only [slopeNumerator, slopeDenominator, if_pos tangent] using slope
      rw [nativeLineAndSum_source]
      simp only [vertical, tangent, Bool.false_eq_true, ↓reduceIte, selected, bind, Except.bind]
      exact finish
    · have selected : nativeDivide (s.y.sub r.y) (s.x.sub r.x) = .ok hint.slope := by
        simpa only [slopeNumerator, slopeDenominator, if_neg tangent] using slope
      rw [nativeLineAndSum_source]
      simp only [vertical, tangent, Bool.false_eq_true, ↓reduceIte, selected, bind, Except.bind]
      exact finish

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.checked_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.divide_product_certificate
#print axioms LeanCrypto.Proofs.BN254Tate.lineHintCheck_sound
