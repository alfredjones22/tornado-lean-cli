import LeanCryptoProofs.NormalizedLine
import LeanCryptoProofs.CurveUnits
open scoped nonZeroDivisors
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate

abbrev FractionIdeal := FractionalIdeal CoordinateRing⁰ FunctionField

def principal (function : FunctionField) (nonzero : function ≠ 0) : FractionIdealˣ :=
  toPrincipalIdeal CoordinateRing FunctionField (Units.mk0 function nonzero)

theorem principal_value (function : FunctionField) (nonzero : function ≠ 0) :
    (principal function nonzero : FractionIdeal) = FractionalIdeal.spanSingleton CoordinateRing⁰ function := by
  simp [principal, coe_toPrincipalIdeal]

theorem principal_one : principal (1 : FunctionField) one_ne_zero = 1 := by
  apply Units.val_injective
  rw [principal_value, FractionalIdeal.spanSingleton_one]
  rfl

theorem principal_vertical (x : BN254Fp12.Field) :
    (principal (verticalFunction x) (verticalFunction_nonzero x) : FractionIdeal) =
      (WeierstrassCurve.Affine.CoordinateRing.XIdeal curve12.toAffine x : FractionIdeal) := by
  rw [principal_value, WeierstrassCurve.Affine.CoordinateRing.XIdeal,
    FractionalIdeal.coeIdeal_span_singleton]
  rfl

theorem principal_line (x y slope : BN254Fp12.Field) :
    (principal (lineFunction x y slope) (lineFunction_nonzero x y slope) : FractionIdeal) =
      (WeierstrassCurve.Affine.CoordinateRing.YIdeal curve12.toAffine
        (WeierstrassCurve.Affine.linePolynomial x y slope) : FractionIdeal) := by
  rw [principal_value, WeierstrassCurve.Affine.CoordinateRing.YIdeal,
    FractionalIdeal.coeIdeal_span_singleton]
  rfl

def pointIdeal : curve12.toAffine.Point → FractionIdealˣ
  | .zero => 1
  | .some _ _ nonsingular => WeierstrassCurve.Affine.CoordinateRing.XYIdeal' nonsingular

theorem principal_vertical_times_quotient (x y slope sumX : BN254Fp12.Field) :
    principal (verticalFunction sumX) (verticalFunction_nonzero sumX) *
      principal (lineQuotient x y slope sumX)
        (div_ne_zero (lineFunction_nonzero x y slope) (verticalFunction_nonzero sumX)) =
      principal (lineFunction x y slope) (lineFunction_nonzero x y slope) := by
  apply Units.val_injective
  simp only [Units.val_mul, principal_value, FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply congrArg (FractionalIdeal.spanSingleton CoordinateRing⁰)
  exact mul_div_cancel₀ _ (verticalFunction_nonzero sumX)

/-- Principal-ideal form of the normalized line divisor relation, derived
from Mathlib's explicit elliptic-curve coordinate-ideal theorem. -/
theorem normalizedLine_principal_relation (first second : curve12.toAffine.Point) :
    principal (normalizedLine first second) (normalizedLine_nonzero first second) *
      pointIdeal (first + second) = pointIdeal first * pointIdeal second := by
  cases first with
  | zero =>
    change principal (1 : FunctionField) _ * pointIdeal second = 1 * pointIdeal second
    rw [principal_one]
  | some x1 y1 h1 =>
    cases second with
    | zero =>
      change principal (1 : FunctionField) _ * pointIdeal (.some x1 y1 h1) = pointIdeal (.some x1 y1 h1) * 1
      rw [principal_one, one_mul, mul_one]
    | some x2 y2 h2 =>
      by_cases vertical : x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2
      · have lineEq : normalizedLine (.some x1 y1 h1) (.some x2 y2 h2) = verticalFunction x1 := by
          change (if x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2 then _ else _) = _
          rw [if_pos vertical]
        simp only [lineEq]
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq vertical.1 vertical.2]
        rcases vertical with ⟨rfl, rfl⟩
        change principal (verticalFunction x1) _ * 1 =
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h1 *
            WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h2
        apply Units.val_injective
        simp only [Units.val_mul, mul_one, principal_vertical,
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq]
        exact congrArg (fun ideal : Ideal CoordinateRing => (ideal : FractionIdeal))
          (WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul h2).symm |>.trans
            (FractionalIdeal.coeIdeal_mul _ _)
      · let slope := curve12.toAffine.slope x1 x2 y1 y2
        let x3 := curve12.toAffine.addX x1 x2 slope
        let y3 := curve12.toAffine.addY x1 x2 y1 slope
        let h3 : curve12.toAffine.Nonsingular x3 y3 :=
          WeierstrassCurve.Affine.nonsingular_add h1 h2 vertical
        have sum := WeierstrassCurve.Affine.Point.add_some (h₁ := h1) (h₂ := h2) vertical
        rw [sum]
        have lineEq : normalizedLine (.some x1 y1 h1) (.some x2 y2 h2) =
            lineQuotient x1 y1 slope x3 := by
          change (if x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2 then _ else _) = _
          rw [if_neg vertical]
        simp only [lineEq]
        change principal (lineQuotient x1 y1 slope x3) _ *
          WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h3 =
            WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h1 *
              WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h2
        let pv := principal (verticalFunction x3) (verticalFunction_nonzero x3)
        let pl := principal (lineFunction x1 y1 slope) (lineFunction_nonzero x1 y1 slope)
        let pq := principal (lineQuotient x1 y1 slope x3)
          (div_ne_zero (lineFunction_nonzero x1 y1 slope) (verticalFunction_nonzero x3))
        have ideals := WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal h1.left h2.left vertical
        have units : pv * (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h1 *
            WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h2) =
              pl * WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h3 := by
          apply Units.val_injective
          simpa only [pv, pl, Units.val_mul, principal_vertical, principal_line,
            WeierstrassCurve.Affine.CoordinateRing.XYIdeal'_eq, FractionalIdeal.coeIdeal_mul] using
              congrArg (fun ideal : Ideal CoordinateRing => (ideal : FractionIdeal)) ideals
        have cancellation : pv * (pq * WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h3) =
            pv * (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h1 *
              WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h2) := by
          rw [← mul_assoc, show pv * pq = pl from principal_vertical_times_quotient x1 y1 slope x3]
          exact units.symm
        exact mul_left_cancel cancellation

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.principal_value
#print axioms LeanCrypto.Proofs.BN254Tate.principal_one
#print axioms LeanCrypto.Proofs.BN254Tate.principal_vertical
#print axioms LeanCrypto.Proofs.BN254Tate.principal_line
#print axioms LeanCrypto.Proofs.BN254Tate.principal_vertical_times_quotient
#print axioms LeanCrypto.Proofs.BN254Tate.normalizedLine_principal_relation
