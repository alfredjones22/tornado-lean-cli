import LeanCryptoProofs.TateMillerNonzero
import LeanCryptoProofs.TateEmbedding
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing BN254Fp12

def sumFromSlope (r s : Point) (slope : Field) : Point :=
  let native := encode slope
  let x := (native.square.sub r.x).sub s.x
  ⟨x, (native.mul (r.x.sub x)).sub r.y⟩

theorem sumFromSlope_x (r s : Point) (slope : Field) :
    model (sumFromSlope r s slope).x = slope ^ 2 - model r.x - model s.x := by
  simp [sumFromSlope]

theorem sumFromSlope_y (r s : Point) (slope : Field) :
    model (sumFromSlope r s slope).y =
      slope * (model r.x - (slope ^ 2 - model r.x - model s.x)) - model r.y := by
  simp [sumFromSlope]

def lineValue (r evaluation : Point) (slope : Field) : Field :=
  (model evaluation.y - model r.y) - slope * (model evaluation.x - model r.x)

def addSlope (r s : Point) : Field := (model s.y - model r.y) / (model s.x - model r.x)

def finishLine (r s evaluation : Point) (slope : Field) : Except String (Fp12 × Option Point) := do
  let sum := sumFromSlope r s slope
  let line := (evaluation.y.sub r.y).sub ((encode slope).mul (evaluation.x.sub r.x))
  let value ← nativeDivide line (evaluation.x.sub sum.x)
  if value == Fp12.zero then throw "BN254 pairing line evaluated to zero."
  return (value, some sum)

theorem finishLine_construct (r s evaluation : Point) (slope : Field)
    (vertical : model evaluation.x - model (sumFromSlope r s slope).x ≠ 0)
    (line : lineValue r evaluation slope ≠ 0) :
    finishLine r s evaluation slope = .ok
      (encode (lineValue r evaluation slope /
        (model evaluation.x - model (sumFromSlope r s slope).x)),
       some (sumFromSlope r s slope)) := by
  unfold finishLine
  let nativeLine := (evaluation.y.sub r.y).sub
    ((encode (slope)).mul (evaluation.x.sub r.x))
  have lineMeaning : model nativeLine = lineValue r evaluation (slope) := by
    simp [nativeLine, lineValue]
  have den : model (evaluation.x.sub (sumFromSlope r s (slope)).x) ≠ 0 := by
    simpa using vertical
  have quotient := divide_construct nativeLine
    (evaluation.x.sub (sumFromSlope r s (slope)).x) den
  rw [lineMeaning, model_sub] at quotient
  change (do
    let value ← nativeDivide nativeLine (evaluation.x.sub (sumFromSlope r s (slope)).x)
    if value == Fp12.zero then throw "BN254 pairing line evaluated to zero."
    return (value, some (sumFromSlope r s (slope)))) = _
  rw [quotient]
  simp only [bind, Except.bind]
  have nonzero : (encode (lineValue r evaluation (slope) /
      (model evaluation.x - model (sumFromSlope r s (slope)).x)) == Fp12.zero) = false := by
    apply Bool.eq_false_iff.mpr
    intro zero
    have zeroMeaning := (model_beq _ _).1 zero
    simp only [model_encode, model_zero] at zeroMeaning
    exact div_ne_zero line vertical zeroMeaning
  simp only [nonzero, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The actual line-and-add constructs the affine field formula from
independent input and evaluation conditions, without a successful-call premise. -/
theorem line_add_construct (r s evaluation : Point)
    (distinctX : model r.x ≠ model s.x)
    (vertical : model evaluation.x - model (sumFromSlope r s (addSlope r s)).x ≠ 0)
    (line : lineValue r evaluation (addSlope r s) ≠ 0) :
    nativeLineAndSum r s evaluation = .ok
      (encode (lineValue r evaluation (addSlope r s) /
        (model evaluation.x - model (sumFromSlope r s (addSlope r s)).x)),
       some (sumFromSlope r s (addSlope r s))) := by
  have different : (r.x == s.x) = false := by
    apply Bool.eq_false_iff.mpr
    exact fun equal => distinctX ((model_beq _ _).1 equal)
  have denNonzero : model (s.x.sub r.x) ≠ 0 := by
    rw [model_sub]
    exact sub_ne_zero.mpr distinctX.symm
  have slope := divide_construct (s.y.sub r.y) (s.x.sub r.x) denNonzero
  simp only [model_sub] at slope
  change nativeDivide (s.y.sub r.y) (s.x.sub r.x) = .ok (encode (addSlope r s)) at slope
  rw [nativeLineAndSum_source]
  simp only [different, Bool.false_and, Bool.false_eq_true, ↓reduceIte, slope,
    bind, Except.bind]
  change finishLine r s evaluation (addSlope r s) = _
  exact finishLine_construct r s evaluation (addSlope r s) vertical line

theorem two_nonzero : (2 : Field) ≠ 0 := by
  intro zero
  have base : (2 : ZMod BN254Fp.P) ≠ 0 := by decide +kernel
  apply base
  apply fpHom.injective
  simpa only [map_ofNat, map_zero] using zero

def doubleSlope (point : Point) : Field := 3 * model point.x ^ 2 / (2 * model point.y)

theorem line_double_construct (point evaluation : Point)
    (nonzeroY : model point.y ≠ 0)
    (vertical : model evaluation.x - model (sumFromSlope point point (doubleSlope point)).x ≠ 0)
    (line : lineValue point evaluation (doubleSlope point) ≠ 0) :
    nativeLineAndSum point point evaluation = .ok
      (encode (lineValue point evaluation (doubleSlope point) /
        (model evaluation.x - model (sumFromSlope point point (doubleSlope point)).x)),
       some (sumFromSlope point point (doubleSlope point))) := by
  have reflexive : (point.x == point.x) = true := (model_beq _ _).2 rfl
  have reflexiveY : (point.y == point.y) = true := (model_beq _ _).2 rfl
  have notNegative : (point.y == point.y.neg) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have negation := (model_beq _ _).1 equal
    rw [model_neg] at negation
    have twice : (2 : Field) * model point.y = 0 := by linear_combination negation
    exact mul_ne_zero two_nonzero nonzeroY twice
  have denNonzero : model (point.y.mul (embedFp (LeanCrypto.BN254.G1.Fp.ofNat 2))) ≠ 0 := by
    rw [model_mul, model_embed_nat]
    exact mul_ne_zero nonzeroY two_nonzero
  have slope := divide_construct
    (point.x.square.mul (embedFp (LeanCrypto.BN254.G1.Fp.ofNat 3)))
    (point.y.mul (embedFp (LeanCrypto.BN254.G1.Fp.ofNat 2))) denNonzero
  simp only [model_mul, model_square, model_embed_nat, Nat.cast_ofNat] at slope
  have slopeEqual : model point.x ^ 2 * 3 / (model point.y * 2) = doubleSlope point := by
    simp only [doubleSlope, mul_comm]
  rw [slopeEqual] at slope
  rw [nativeLineAndSum_source]
  simp only [reflexive, reflexiveY, notNegative, Bool.true_and, Bool.false_eq_true,
    ↓reduceIte, slope, bind, Except.bind]
  change finishLine point point evaluation (doubleSlope point) = _
  exact finishLine_construct point point evaluation (doubleSlope point) vertical line

theorem line_vertical_construct (r s evaluation : Point)
    (sameX : model r.x = model s.x) (negativeY : model r.y = -model s.y)
    (vertical : model evaluation.x - model r.x ≠ 0) :
    nativeLineAndSum r s evaluation = .ok (evaluation.x.sub r.x, none) := by
  have xGuard : (r.x == s.x) = true := (model_beq _ _).2 sameX
  have yGuard : (r.y == s.y.neg) = true := (model_beq _ _).2 (by simpa using negativeY)
  have nonzero : (evaluation.x.sub r.x == Fp12.zero) = false := by
    apply Bool.eq_false_iff.mpr
    intro zero
    have equal := (model_beq _ _).1 zero
    rw [model_sub, model_zero] at equal
    exact vertical equal
  rw [nativeLineAndSum_source]
  simp only [xGuard, yGuard, Bool.true_and, ↓reduceIte, nonzero, Bool.false_eq_true,
    pure_bind]
  rfl

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.sumFromSlope_x
#print axioms LeanCrypto.Proofs.BN254Tate.sumFromSlope_y
#print axioms LeanCrypto.Proofs.BN254Tate.finishLine_construct
#print axioms LeanCrypto.Proofs.BN254Tate.line_add_construct
#print axioms LeanCrypto.Proofs.BN254Tate.two_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.line_double_construct
#print axioms LeanCrypto.Proofs.BN254Tate.line_vertical_construct
