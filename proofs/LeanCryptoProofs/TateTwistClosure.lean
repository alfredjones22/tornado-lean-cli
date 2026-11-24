import LeanCryptoProofs.TateAffineConstruction
import LeanCryptoProofs.TateTwistNonzero
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing

theorem point_ext {left right : Point} (x : left.x = right.x) (y : left.y = right.y) : left = right := by
  cases left
  cases right
  cases x
  cases y
  rfl

def g2SumFromSlope (r s : Affine) (slope : BN254Fp2.Field) : Affine :=
  let x := slope ^ 2 - BN254Fp2.model r.x - BN254Fp2.model s.x
  let y := slope * (BN254Fp2.model r.x - x) - BN254Fp2.model r.y
  ⟨BN254Fp2.encode x, BN254Fp2.encode y⟩

theorem sumFromSlope_twist (r s : Affine) (slope : BN254Fp2.Field) :
    sumFromSlope (embedG2 r) (embedG2 s) (slopeValue slope) =
      embedG2 (g2SumFromSlope r s slope) := by
  have x : (sumFromSlope (embedG2 r) (embedG2 s) (slopeValue slope)).x =
      (embedG2 (g2SumFromSlope r s slope)).x := by
    apply BN254Fp12.model_injective
    rw [sumFromSlope_x, model_embedG2_x, model_embedG2_x, model_embedG2_x]
    simp only [g2SumFromSlope, BN254Fp2.model_encode, map_sub, map_pow, slopeValue]
    apply QuadraticAlgebra.ext <;> simp [pow_succ, BN254Fp6.model_v]; ring
  have y : (sumFromSlope (embedG2 r) (embedG2 s) (slopeValue slope)).y =
      (embedG2 (g2SumFromSlope r s slope)).y := by
    apply BN254Fp12.model_injective
    rw [sumFromSlope_y, model_embedG2_x, model_embedG2_x, model_embedG2_y, model_embedG2_y]
    simp only [g2SumFromSlope, BN254Fp2.model_encode, map_sub, map_pow, map_mul, slopeValue]
    apply QuadraticAlgebra.ext <;> simp [pow_succ, BN254Fp6.model_v]; ring
  exact point_ext x y

theorem imaginary_div_real (a b : BN254Fp6.Field) (nonzero : b ≠ 0) :
    (⟨0, a⟩ : BN254Fp12.Field) / ⟨b, 0⟩ = ⟨0, a / b⟩ := by
  have denominator : (⟨b, 0⟩ : BN254Fp12.Field) ≠ 0 := by
    intro zero
    exact nonzero (congrArg QuadraticAlgebra.re zero)
  apply (div_eq_iff denominator).mpr
  apply QuadraticAlgebra.ext
  · simp
  · simpa using (div_mul_cancel₀ a nonzero).symm

theorem distinct_twist_x (r s : Affine) (distinct : BN254Fp2.model r.x ≠ BN254Fp2.model s.x) :
    BN254Fp12.model (embedG2 r).x ≠ BN254Fp12.model (embedG2 s).x := by
  intro equal
  rw [model_embedG2_x, model_embedG2_x] at equal
  have realPart := congrArg QuadraticAlgebra.re equal
  have vNonzero : AdjoinRoot.root BN254Fp6.cubic ≠ 0 := by
    simpa using BN254Fp6.v_nonzero
  have coefficients := mul_right_cancel₀ vNonzero realPart
  exact distinct ((algebraMap BN254Fp2.Field BN254Fp6.Field).injective coefficients)

theorem addSlope_twist (r s : Affine)
    (distinct : BN254Fp2.model r.x ≠ BN254Fp2.model s.x) :
    addSlope (embedG2 r) (embedG2 s) =
      slopeValue ((BN254Fp2.model s.y - BN254Fp2.model r.y) /
        (BN254Fp2.model s.x - BN254Fp2.model r.x)) := by
  rw [addSlope, model_embedG2_y, model_embedG2_y, model_embedG2_x, model_embedG2_x]
  let lift := AdjoinRoot.of BN254Fp6.cubic
  let v := AdjoinRoot.root BN254Fp6.cubic
  have vNonzero : v ≠ 0 := by simpa only [v, BN254Fp6.model_v] using BN254Fp6.v_nonzero
  have denNonzero : lift (BN254Fp2.model s.x - BN254Fp2.model r.x) ≠ 0 := by
    exact fun zero => sub_ne_zero.mpr distinct.symm (lift.injective (by simpa using zero))
  have productNonzero : lift (BN254Fp2.model s.x) * v - lift (BN254Fp2.model r.x) * v ≠ 0 := by
    rw [← sub_mul, ← map_sub]
    exact mul_ne_zero denNonzero vNonzero
  simp only [QuadraticAlgebra.mk_sub_mk, sub_self]
  change (⟨0, lift (BN254Fp2.model s.y) * v - lift (BN254Fp2.model r.y) * v⟩ : BN254Fp12.Field) /
    ⟨lift (BN254Fp2.model s.x) * v - lift (BN254Fp2.model r.x) * v, 0⟩ = _
  rw [imaginary_div_real _ _ productNonzero]
  apply QuadraticAlgebra.ext
  · rfl
  · change _ = lift ((BN254Fp2.model s.y - BN254Fp2.model r.y) /
      (BN254Fp2.model s.x - BN254Fp2.model r.x))
    rw [map_div₀, map_sub, map_sub, ← sub_mul, ← sub_mul]
    exact mul_div_mul_right _ _ vNonzero

/-- Native affine addition of any two distinct-x twist representatives
constructs another twist representative, and every evaluation guard is
discharged for any independently on-curve finite G1 point. -/
theorem twist_add_construct (r s : Affine) (evaluation : LeanCrypto.BN254.G1.Affine)
    (onCurve : evaluation.onCurve = true)
    (distinct : BN254Fp2.model r.x ≠ BN254Fp2.model s.x) :
    ∃ factor : Fp12,
      nativeLineAndSum (embedG2 r) (embedG2 s) (embedG1 evaluation) = .ok
        (factor, some (embedG2 (g2SumFromSlope r s
          ((BN254Fp2.model s.y - BN254Fp2.model r.y) /
            (BN254Fp2.model s.x - BN254Fp2.model r.x))))) := by
  let slope := (BN254Fp2.model s.y - BN254Fp2.model r.y) /
    (BN254Fp2.model s.x - BN254Fp2.model r.x)
  have slopeShape : addSlope (embedG2 r) (embedG2 s) = slopeValue slope := addSlope_twist r s distinct
  have sumShape : sumFromSlope (embedG2 r) (embedG2 s) (addSlope (embedG2 r) (embedG2 s)) =
      embedG2 (g2SumFromSlope r s slope) := by rw [slopeShape, sumFromSlope_twist]
  have vertical : BN254Fp12.model (embedG1 evaluation).x -
      BN254Fp12.model (sumFromSlope (embedG2 r) (embedG2 s) (addSlope (embedG2 r) (embedG2 s))).x ≠ 0 := by
    rw [sumShape]
    exact twist_vertical_nonzero evaluation onCurve _
  have line : lineValue (embedG2 r) (embedG1 evaluation) (addSlope (embedG2 r) (embedG2 s)) ≠ 0 := by
    rw [slopeShape]
    exact twist_line_nonzero evaluation onCurve r slope
  have constructed := line_add_construct (embedG2 r) (embedG2 s) (embedG1 evaluation)
    (distinct_twist_x r s distinct) vertical line
  rw [sumShape] at constructed
  exact ⟨_, constructed⟩

theorem nonzero_twist_y (point : Affine) (nonzero : BN254Fp2.model point.y ≠ 0) :
    BN254Fp12.model (embedG2 point).y ≠ 0 := by
  intro zero
  rw [model_embedG2_y] at zero
  have imaginary := congrArg QuadraticAlgebra.im zero
  have vNonzero : AdjoinRoot.root BN254Fp6.cubic ≠ 0 := by simpa using BN254Fp6.v_nonzero
  have liftedNonzero : (algebraMap BN254Fp2.Field BN254Fp6.Field) (BN254Fp2.model point.y) ≠ 0 :=
    fun equal => nonzero ((algebraMap BN254Fp2.Field BN254Fp6.Field).injective (by simpa using equal))
  exact mul_ne_zero liftedNonzero vNonzero imaginary

theorem doubleSlope_twist (point : Affine) (nonzero : BN254Fp2.model point.y ≠ 0) :
    doubleSlope (embedG2 point) = slopeValue
      (3 * BN254Fp2.model point.x ^ 2 / (2 * BN254Fp2.model point.y)) := by
  let lift := AdjoinRoot.of BN254Fp6.cubic
  let x := BN254Fp2.model point.x
  let y := BN254Fp2.model point.y
  let v := AdjoinRoot.root BN254Fp6.cubic
  let slope := 3 * x ^ 2 / (2 * y)
  have denominator : (2 : BN254Fp12.Field) * BN254Fp12.model (embedG2 point).y ≠ 0 :=
    mul_ne_zero two_nonzero (nonzero_twist_y point nonzero)
  have denominator2 : (2 : BN254Fp2.Field) * y ≠ 0 :=
    mul_ne_zero (by decide +kernel) nonzero
  have slopeEquation : slope * (2 * y) = 3 * x ^ 2 := div_mul_cancel₀ _ denominator2
  have lifted := congrArg lift slopeEquation
  simp only [map_mul, map_pow, map_ofNat] at lifted
  rw [doubleSlope]
  apply (div_eq_iff denominator).mpr
  rw [model_embedG2_x, model_embedG2_y]
  change 3 * (⟨lift x * v, 0⟩ : BN254Fp12.Field) ^ 2 =
    slopeValue slope * (2 * (⟨0, lift y * v⟩ : BN254Fp12.Field))
  apply QuadraticAlgebra.ext
  · simp [pow_succ, slopeValue, BN254Fp6.model_v, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
    calc
      _ = (3 * lift x ^ 2) * v ^ 2 := by ring
      _ = (lift slope * (2 * lift y)) * v ^ 2 := by rw [lifted]
      _ = _ := by ring
  · simp [pow_succ, slopeValue, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

theorem twist_double_construct (point : Affine) (evaluation : LeanCrypto.BN254.G1.Affine)
    (onCurve : evaluation.onCurve = true) (nonzeroY : BN254Fp2.model point.y ≠ 0) :
    ∃ factor : Fp12,
      nativeLineAndSum (embedG2 point) (embedG2 point) (embedG1 evaluation) = .ok
        (factor, some (embedG2 (g2SumFromSlope point point
          (3 * BN254Fp2.model point.x ^ 2 / (2 * BN254Fp2.model point.y))))) := by
  let slope := 3 * BN254Fp2.model point.x ^ 2 / (2 * BN254Fp2.model point.y)
  have slopeShape : doubleSlope (embedG2 point) = slopeValue slope := doubleSlope_twist point nonzeroY
  have sumShape : sumFromSlope (embedG2 point) (embedG2 point) (doubleSlope (embedG2 point)) =
      embedG2 (g2SumFromSlope point point slope) := by rw [slopeShape, sumFromSlope_twist]
  have vertical : BN254Fp12.model (embedG1 evaluation).x -
      BN254Fp12.model (sumFromSlope (embedG2 point) (embedG2 point) (doubleSlope (embedG2 point))).x ≠ 0 := by
    rw [sumShape]
    exact twist_vertical_nonzero evaluation onCurve _
  have line : lineValue (embedG2 point) (embedG1 evaluation) (doubleSlope (embedG2 point)) ≠ 0 := by
    rw [slopeShape]
    exact twist_line_nonzero evaluation onCurve point slope
  have constructed := line_double_construct (embedG2 point) (embedG1 evaluation)
    (nonzero_twist_y point nonzeroY) vertical line
  rw [sumShape] at constructed
  exact ⟨_, constructed⟩

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.point_ext
#print axioms LeanCrypto.Proofs.BN254Tate.sumFromSlope_twist
#print axioms LeanCrypto.Proofs.BN254Tate.imaginary_div_real
#print axioms LeanCrypto.Proofs.BN254Tate.distinct_twist_x
#print axioms LeanCrypto.Proofs.BN254Tate.addSlope_twist
#print axioms LeanCrypto.Proofs.BN254Tate.twist_add_construct
#print axioms LeanCrypto.Proofs.BN254Tate.nonzero_twist_y
#print axioms LeanCrypto.Proofs.BN254Tate.doubleSlope_twist
#print axioms LeanCrypto.Proofs.BN254Tate.twist_double_construct
