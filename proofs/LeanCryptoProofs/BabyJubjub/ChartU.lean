import LeanCryptoProofs.BabyJubjub.ChartCrossU

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace LeanCrypto.Proofs.BabyJubjubCharts
open LeanCrypto.Proofs.BabyJubjub

def regularSlope (x y z w : Field) : Field := (chartV z w-chartV x y)/(chartU w-chartU y)
def regularU (x y z w : Field) : Field := (regularSlope x y z w)^2-168698-chartU y-chartU w

def regularV (x y z w : Field) : Field :=
  -chartV x y-regularSlope x y z w*(regularU x y z w-chartU y)

theorem chart_difference_nonzero (y w : Field) (different : chartU y ≠ chartU w) : y ≠ w := by
  intro equal
  exact different (congrArg chartU equal)

theorem chartU_difference (y w : Field) (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) :
    chartU w-chartU y = 2*(w-y)/((1-w)*(1-y)) := by
  unfold chartU
  field_simp [yChart,wChart]
  ring

theorem chartV_difference (x y z w : Field) (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) :
    chartV z w-chartV x y = ((1+w)*(1-y)*x-(1+y)*(1-w)*z)/((1-w)*(1-y)*x*z) := by
  unfold chartV chartU
  field_simp [xNonzero,zNonzero,yChart,wChart]

theorem regularSlope_explicit (x y z w : Field) (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : y ≠ w) :
    regularSlope x y z w = ((1+w)*(1-y)*x-(1+y)*(1-w)*z)/(2*(w-y)*x*z) := by
  unfold regularSlope
  rw [chartU_difference y w yChart wChart, chartV_difference x y z w xNonzero zNonzero yChart wChart]
  have otherDifference : w-y ≠ 0 := sub_ne_zero.mpr different.symm
  field_simp [xNonzero,zNonzero,yChart,wChart,otherDifference]

theorem numerator_u_representation (x y z w : Field)
    (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : y ≠ w)
    (minus : 1-168696*x*z*y*w ≠ 0) :
    ((1-edwardsAddY x y z w)*regularU x y z w-(1+edwardsAddY x y z w))*
      denominator_u x y z w = numerator_u x y z w := by
  unfold regularU
  rw [regularSlope_explicit x y z w xNonzero zNonzero yChart wChart different]
  have otherDifference : w-y ≠ 0 := sub_ne_zero.mpr different.symm
  have twoNonzero : (2 : Field) ≠ 0 := by decide +kernel
  have fourNonzero : (4 : Field) ≠ 0 := by decide +kernel
  have modMinus : 1-y*w*x*z*168696 ≠ 0 := by
    convert minus using 1; ring
  unfold edwardsAddY chartU denominator_u numerator_u
  field_simp [xNonzero,zNonzero,yChart,wChart,otherDifference,minus,twoNonzero,fourNonzero,modMinus]
  field_simp [twoNonzero,fourNonzero,modMinus]
  ring

theorem denominator_u_nonzero (x y z w : Field)
    (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : y ≠ w)
    (minus : 1-168696*x*z*y*w ≠ 0) : denominator_u x y z w ≠ 0 := by
  have difference : -w+y ≠ 0 := by simpa only [sub_eq_add_neg, add_comm] using sub_ne_zero.mpr different
  have yOne : y-1 ≠ 0 := sub_ne_zero.mpr (by intro equal; exact yChart (by rw [equal]; ring))
  have wOne : w-1 ≠ 0 := sub_ne_zero.mpr (by intro equal; exact wChart (by rw [equal]; ring))
  have negativeMinus : 168696*w*x*y*z-1 ≠ 0 := by
    convert neg_ne_zero.mpr minus using 1; ring
  simp [denominator_u,xNonzero,zNonzero,difference,yOne,wOne,negativeMinus]
  decide +kernel

theorem regular_chart_cross_u (x y z w : Field) (first : Edwards x y) (second : Edwards z w)
    (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : chartU y ≠ chartU w) :
    (1-edwardsAddY x y z w)*regularU x y z w = 1+edwardsAddY x y z w := by
  have yDifferent := chart_difference_nonzero y w different
  have minus := (LeanCrypto.Proofs.BabyJubjubComplete.babyjub_complete_denominators x y z w first second).2
  have represented := numerator_u_representation x y z w xNonzero zNonzero yChart wChart yDifferent minus
  rw [numerator_u_zero x y z w first second] at represented
  exact sub_eq_zero.mp ((mul_eq_zero.mp represented).resolve_right
    (denominator_u_nonzero x y z w xNonzero zNonzero yChart wChart yDifferent minus))

theorem regular_output_chart_nonzero (x y z w : Field) (first : Edwards x y) (second : Edwards z w)
    (xNonzero : x ≠ 0) (zNonzero : z ≠ 0)
    (yChart : 1-y ≠ 0) (wChart : 1-w ≠ 0) (different : chartU y ≠ chartU w) :
    1-edwardsAddY x y z w ≠ 0 := by
  intro zero
  have cross := regular_chart_cross_u x y z w first second xNonzero zNonzero yChart wChart different
  rw [zero, zero_mul] at cross
  have one : edwardsAddY x y z w = 1 := (sub_eq_zero.mp zero).symm
  rw [one] at cross
  exact (by decide +kernel : (0 : Field) ≠ 1+1) cross

end LeanCrypto.Proofs.BabyJubjubCharts
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.chart_difference_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.numerator_u_representation
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.denominator_u_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.regular_chart_cross_u
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.regular_output_chart_nonzero

#print axioms LeanCrypto.Proofs.BabyJubjubCharts.chartU_difference
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.chartV_difference
#print axioms LeanCrypto.Proofs.BabyJubjubCharts.regularSlope_explicit
