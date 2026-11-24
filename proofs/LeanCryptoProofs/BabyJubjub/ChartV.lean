import LeanCryptoProofs.BabyJubjub.ChartU
import LeanCryptoProofs.BabyJubjub.ChartCrossV

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace LeanCrypto.Proofs.BabyJubjubCharts
open LeanCrypto.Proofs.BabyJubjub

theorem numerator_v_representation (x y z w : Field)
    (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : y ≠ w)
    (plus : 1+168696*x*z*y*w ≠ 0) :
    (edwardsAddX x y z w*regularV x y z w-regularU x y z w)*
      denominator_v x y z w = numerator_v x y z w := by
  unfold regularV regularU
  simp only [regularSlope_explicit x y z w xNonzero zNonzero yChart wChart different]
  have otherDifference : w-y ≠ 0 := sub_ne_zero.mpr different.symm
  have twoNonzero : (2 : Field) ≠ 0 := by decide +kernel
  have fourNonzero : (4 : Field) ≠ 0 := by decide +kernel
  have eightNonzero : (8 : Field) ≠ 0 := by decide +kernel
  have modPlus : y*w*x*z*168696+1 ≠ 0 := by
    convert plus using 1; ring
  have orderedPlus : 1+x*w*y*z*168696 ≠ 0 := by
    convert plus using 1; ring
  unfold edwardsAddX chartV chartU denominator_v numerator_v
  field_simp [xNonzero,zNonzero,yChart,wChart,otherDifference,plus,twoNonzero,fourNonzero,eightNonzero,modPlus,orderedPlus]
  field_simp [twoNonzero,fourNonzero,eightNonzero,modPlus,orderedPlus]
  ring

theorem denominator_v_nonzero (x y z w : Field)
    (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : y ≠ w)
    (plus : 1+168696*x*z*y*w ≠ 0) : denominator_v x y z w ≠ 0 := by
  have difference : -w+y ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr different
  have yOne : y-1 ≠ 0 := sub_ne_zero.mpr (by intro equal; exact yChart (by rw [equal]; ring))
  have wOne : w-1 ≠ 0 := sub_ne_zero.mpr (by intro equal; exact wChart (by rw [equal]; ring))
  have reorderedPlus : 168696*w*x*y*z+1 ≠ 0 := by
    convert plus using 1; ring
  simp [denominator_v,xNonzero,zNonzero,difference,yOne,wOne,reorderedPlus]
  decide +kernel

theorem regular_chart_cross_v (x y z w : Field) (first : Edwards x y) (second : Edwards z w)
    (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : chartU y ≠ chartU w) :
    edwardsAddX x y z w*regularV x y z w = regularU x y z w := by
  have yDifferent := chart_difference_nonzero y w different
  have plus := (LeanCrypto.Proofs.BabyJubjubComplete.babyjub_complete_denominators x y z w first second).1
  have represented := numerator_v_representation x y z w xNonzero zNonzero yChart wChart yDifferent plus
  rw [numerator_v_zero x y z w first second] at represented
  exact sub_eq_zero.mp ((mul_eq_zero.mp represented).resolve_right
    (denominator_v_nonzero x y z w xNonzero zNonzero yChart wChart yDifferent plus))

theorem actual_slope_regular (x y z w : Field) (different : chartU y ≠ chartU w) :
    curve.slope (chartU y) (chartU w) (chartV x y) (chartV z w) = regularSlope x y z w := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne different]
  unfold regularSlope
  apply (div_eq_div_iff (sub_ne_zero.mpr different) (sub_ne_zero.mpr different.symm)).2
  ring

theorem actual_addX_regular (x y z w : Field) (different : chartU y ≠ chartU w) :
    curve.addX (chartU y) (chartU w)
      (curve.slope (chartU y) (chartU w) (chartV x y) (chartV z w)) = regularU x y z w := by
  rw [actual_slope_regular x y z w different]
  simp only [WeierstrassCurve.Affine.addX,curve,zero_mul,add_zero]
  rfl

theorem actual_addY_regular (x y z w : Field) (different : chartU y ≠ chartU w) :
    curve.addY (chartU y) (chartU w) (chartV x y)
      (curve.slope (chartU y) (chartU w) (chartV x y) (chartV z w)) = regularV x y z w := by
  rw [actual_slope_regular x y z w different]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
    WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.addX curve regularV regularU
  ring

theorem chart_addX_regular (x y z w : Field) (first : Edwards x y) (second : Edwards z w)
    (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : chartU y ≠ chartU w) :
    chartU (edwardsAddY x y z w) = curve.addX (chartU y) (chartU w)
      (curve.slope (chartU y) (chartU w) (chartV x y) (chartV z w)) := by
  rw [actual_addX_regular x y z w different]
  unfold chartU
  apply (div_eq_iff (regular_output_chart_nonzero x y z w first second xNonzero zNonzero yChart wChart different)).2
  simpa only [mul_comm] using (regular_chart_cross_u x y z w first second xNonzero zNonzero yChart wChart different).symm

theorem chart_addY_regular (x y z w : Field) (first : Edwards x y) (second : Edwards z w)
    (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : chartU y ≠ chartU w)
    (outputNonzero : edwardsAddX x y z w ≠ 0) :
    chartV (edwardsAddX x y z w) (edwardsAddY x y z w) =
      curve.addY (chartU y) (chartU w) (chartV x y)
        (curve.slope (chartU y) (chartU w) (chartV x y) (chartV z w)) := by
  rw [actual_addY_regular x y z w different]
  unfold chartV
  apply (div_eq_iff outputNonzero).2
  rw [chart_addX_regular x y z w first second xNonzero zNonzero yChart wChart different,
    actual_addX_regular x y z w different]
  simpa only [mul_comm] using (regular_chart_cross_v x y z w first second xNonzero zNonzero yChart wChart different).symm

end LeanCrypto.Proofs.BabyJubjubCharts
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.numerator_v_representation
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.denominator_v_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.regular_chart_cross_v
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.actual_slope_regular
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.actual_addX_regular
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.actual_addY_regular
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.chart_addX_regular
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.chart_addY_regular
