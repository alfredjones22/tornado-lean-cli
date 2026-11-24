import LeanCryptoProofs.FunctionStar
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate

def IsTwistPoint : curve12.toAffine.Point → Prop
  | .zero => True
  | .some x y _ => star x = x ∧ star y = -y

theorem curve12_addX (x1 x2 slope : BN254Fp12.Field) :
    curve12.toAffine.addX x1 x2 slope = slope ^ 2 - x1 - x2 := by
  simp [WeierstrassCurve.Affine.addX, curve12_coefficients]

theorem curve12_addY (x1 x2 y1 slope : BN254Fp12.Field) :
    curve12.toAffine.addY x1 x2 y1 slope = slope * (x1 - (slope ^ 2 - x1 - x2)) - y1 := by
  simp [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX, curve12_coefficients]
  ring

theorem star_curve_slope (x1 x2 y1 y2 : BN254Fp12.Field)
    (realX1 : star x1 = x1) (realX2 : star x2 = x2)
    (imaginaryY1 : star y1 = -y1) (imaginaryY2 : star y2 = -y2) :
    star (curve12.toAffine.slope x1 x2 y1 y2) = -curve12.toAffine.slope x1 x2 y1 y2 := by
  by_cases same : x1 = x2
  · by_cases negative : y1 = curve12.toAffine.negY x2 y2
    · rw [WeierstrassCurve.Affine.slope_of_Y_eq same negative]
      simp
    · have formula : curve12.toAffine.slope x1 x2 y1 y2 = 3 * x1 ^ 2 / (y1 + y1) := by
        rw [WeierstrassCurve.Affine.slope_of_Y_ne same negative]
        simp [curve12_coefficients, WeierstrassCurve.Affine.negY]
      rw [formula, star_div₀, star_mul, star_pow, realX1, star_ofNat, star_add, imaginaryY1,
        ← neg_add, div_neg]
      ring
  · rw [WeierstrassCurve.Affine.slope_of_X_ne same, star_div₀, star_sub, star_sub,
      imaginaryY1, imaginaryY2, realX1, realX2]
    ring

theorem star_sumX (x1 x2 slope : BN254Fp12.Field)
    (realX1 : star x1 = x1) (realX2 : star x2 = x2) (imaginarySlope : star slope = -slope) :
    star (slope ^ 2 - x1 - x2) = slope ^ 2 - x1 - x2 := by
  rw [star_sub, star_sub, star_pow, imaginarySlope, realX1, realX2, neg_sq]

theorem star_sumY (x1 x2 y1 slope : BN254Fp12.Field)
    (realX1 : star x1 = x1) (realX2 : star x2 = x2)
    (imaginaryY1 : star y1 = -y1) (imaginarySlope : star slope = -slope) :
    star (slope * (x1 - (slope ^ 2 - x1 - x2)) - y1) =
      -(slope * (x1 - (slope ^ 2 - x1 - x2)) - y1) := by
  rw [star_sub, star_mul, star_sub, star_sumX x1 x2 slope realX1 realX2 imaginarySlope,
    realX1, imaginaryY1, imaginarySlope]
  ring

theorem twistPoint_zero : IsTwistPoint 0 := trivial

theorem twistPoint_neg (point : curve12.toAffine.Point) (admitted : IsTwistPoint point) :
    IsTwistPoint (-point) := by
  cases point with
  | zero => trivial
  | some x y nonsingular =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    change star x = x ∧ star (curve12.toAffine.negY x y) = -curve12.toAffine.negY x y
    have inputs : star x = x ∧ star y = -y := admitted
    constructor
    · exact inputs.1
    · simp [curve12_coefficients, WeierstrassCurve.Affine.negY, inputs.2]

theorem twistPoint_add (first second : curve12.toAffine.Point)
    (firstAdmitted : IsTwistPoint first) (secondAdmitted : IsTwistPoint second) :
    IsTwistPoint (first + second) := by
  cases first with
  | zero => exact secondAdmitted
  | some x1 y1 h1 =>
    cases second with
    | zero => exact firstAdmitted
    | some x2 y2 h2 =>
      have inputs1 : star x1 = x1 ∧ star y1 = -y1 := firstAdmitted
      have inputs2 : star x2 = x2 ∧ star y2 = -y2 := secondAdmitted
      by_cases vertical : x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2
      · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq vertical.1 vertical.2]
        trivial
      · rw [WeierstrassCurve.Affine.Point.add_some vertical]
        change star (curve12.toAffine.addX x1 x2 _) = curve12.toAffine.addX x1 x2 _ ∧
          star (curve12.toAffine.addY x1 x2 y1 _) = -curve12.toAffine.addY x1 x2 y1 _
        have slope := star_curve_slope x1 x2 y1 y2 inputs1.1 inputs2.1 inputs1.2 inputs2.2
        simpa only [curve12_addX, curve12_addY] using And.intro
          (star_sumX x1 x2 _ inputs1.1 inputs2.1 slope)
          (star_sumY x1 x2 y1 _ inputs1.1 inputs2.1 inputs1.2 slope)

def twistSubgroup : AddSubgroup curve12.toAffine.Point where
  carrier := IsTwistPoint
  zero_mem' := twistPoint_zero
  add_mem' := by intro first second h1 h2; exact twistPoint_add first second h1 h2
  neg_mem' := by intro point h; exact twistPoint_neg point h

theorem native_embed_twist (point : LeanCrypto.BN254.G2.Affine) (onCurve : point.onCurve = true) :
    IsTwistPoint (modelPoint (LeanCrypto.BN254.TatePairing.embedG2 point) (embedG2_onCurve point onCurve)) := by
  change star (BN254Fp12.model (LeanCrypto.BN254.TatePairing.embedG2 point).x) = _ ∧
    star (BN254Fp12.model (LeanCrypto.BN254.TatePairing.embedG2 point).y) = _
  rw [model_embedG2_x, model_embedG2_y]
  constructor <;> apply QuadraticAlgebra.ext <;> simp

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.curve12_addX
#print axioms LeanCrypto.Proofs.BN254Tate.curve12_addY
#print axioms LeanCrypto.Proofs.BN254Tate.star_curve_slope
#print axioms LeanCrypto.Proofs.BN254Tate.star_sumX
#print axioms LeanCrypto.Proofs.BN254Tate.star_sumY
#print axioms LeanCrypto.Proofs.BN254Tate.twistPoint_zero
#print axioms LeanCrypto.Proofs.BN254Tate.twistPoint_neg
#print axioms LeanCrypto.Proofs.BN254Tate.twistPoint_add
#print axioms LeanCrypto.Proofs.BN254Tate.native_embed_twist
