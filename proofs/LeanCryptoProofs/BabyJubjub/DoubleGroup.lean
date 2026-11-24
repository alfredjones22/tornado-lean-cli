import LeanCryptoProofs.BabyJubjub.DoubleChart
import LeanCryptoProofs.BabyJubjub.EdwardsBasic

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace LeanCrypto.Proofs.BabyJubjub

theorem regular_plus_nonzero (p : EPoint) (nonzeroX : p.x≠0) : 1+p.y≠0 := by
  intro zero
  have y : p.y= -1 := by linear_combination zero
  exact nonzeroX (edwards_y_neg_one _ _ p.onCurve y)

theorem regular_v_nonzero (p : EPoint) (nonzeroX : p.x≠0) (finite : p.y≠1) :
    chartV p.x p.y≠0 :=
  div_ne_zero (div_ne_zero (regular_plus_nonzero p nonzeroX) (sub_ne_zero.mpr finite.symm)) nonzeroX

theorem regular_v_not_neg (p : EPoint) (nonzeroX : p.x≠0) (finite : p.y≠1) :
    chartV p.x p.y≠curve.negY (chartU p.y) (chartV p.x p.y) := by
  have nonzero := mul_ne_zero (by decide +kernel : (2:Field)≠0) (regular_v_nonzero p nonzeroX finite)
  simp only [WeierstrassCurve.Affine.negY,curve,zero_mul,sub_zero]
  intro equal
  apply nonzero
  linear_combination equal

theorem double_math_slope (p : EPoint) (nonzeroX : p.x≠0) (finite : p.y≠1) :
    curve.slope (chartU p.y) (chartU p.y) (chartV p.x p.y) (chartV p.x p.y)=doubleSlope p.x p.y := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (regular_v_not_neg p nonzeroX finite)]
  simp only [WeierstrassCurve.Affine.negY,curve,zero_mul,sub_zero]
  unfold doubleSlope
  congr 1
  ring

theorem double_math_coordinates (p : EPoint) (nonzeroX : p.x≠0) (finite : p.y≠1) :
    curve.addX (chartU p.y) (chartU p.y)
        (curve.slope (chartU p.y) (chartU p.y) (chartV p.x p.y) (chartV p.x p.y))=doubleU p.x p.y ∧
    curve.addY (chartU p.y) (chartU p.y) (chartV p.x p.y)
        (curve.slope (chartU p.y) (chartU p.y) (chartV p.x p.y) (chartV p.x p.y))=doubleV p.x p.y := by
  rw [double_math_slope p nonzeroX finite]
  constructor
  · simp only [WeierstrassCurve.Affine.addX,curve,zero_mul,add_zero,doubleU]
    ring
  · simp only [WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.negY,curve,zero_mul,add_zero,sub_zero,doubleV,doubleU]
    ring

theorem montgomery_zero_x (u v : Field) (equation : Montgomery u v) (zero : u=0) : v=0 := by
  have square : v^2=0 := by
    simpa only [Montgomery,zero,zero_pow (by decide : 2≠0),
      zero_pow (by decide : 3≠0),mul_zero,add_zero] using equation
  exact (pow_eq_zero_iff (by decide : 2≠0)).mp square

theorem toMontgomery_double_regular (p : EPoint) (nonzeroX : p.x≠0) (finite : p.y≠1) :
    toMontgomery (p.add p)=toMontgomery p+toMontgomery p := by
  have plus := regular_plus_nonzero p nonzeroX
  have minus : 1-p.y≠0 := sub_ne_zero.mpr finite.symm
  have finiteAfter : (p.add p).y≠1 := doubleY_finite _ _ p.onCurve nonzeroX
  have sourceEquation := (montgomery_equation _ _).mp (chart_curve _ _ p.onCurve finite)
  let nonsingular : curve.Nonsingular (chartU p.y) (chartV p.x p.y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp sourceEquation
  have source : toMontgomery p=WeierstrassCurve.Affine.Point.some (chartU p.y) (chartV p.x p.y) nonsingular := by
    simp only [toMontgomery,finite,↓reduceDIte,WeierstrassCurve.Affine.Point.mk]
  have yDifferent := regular_v_not_neg p nonzeroX finite
  have addition := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁:=nonsingular) yDifferent
  rw [source,addition,toMontgomery,dif_neg finiteAfter]
  change WeierstrassCurve.Affine.Point.some
      (chartU (edwardsAddY p.x p.y p.x p.y))
      (chartV (edwardsAddX p.x p.y p.x p.y) (edwardsAddY p.x p.y p.x p.y)) _ = _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  have coordinates := double_math_coordinates p nonzeroX finite
  have xEquation := (doubleU_chart _ _ p.onCurve nonzeroX plus minus).trans coordinates.1.symm
  refine ⟨xEquation,?_⟩
  by_cases yZero : p.y=0
  · have ax : 168700*p.x^2=1 := by simpa only [Edwards,yZero,zero_pow (by decide : 2≠0),add_zero,mul_zero] using p.onCurve
    have afterY : edwardsAddY p.x p.y p.x p.y= -1 := by
      simp only [edwardsAddY,yZero,mul_zero,zero_sub,sub_zero,div_one]
      linear_combination -ax
    have uZero : chartU (edwardsAddY p.x p.y p.x p.y)=0 := by simp only [afterY,chartU,add_neg_cancel,zero_div]
    have leftZero : chartV (edwardsAddX p.x p.y p.x p.y) (edwardsAddY p.x p.y p.x p.y)=0 := by
      unfold chartV
      rw [uZero,zero_div]
    have afterNonsingular := WeierstrassCurve.Affine.nonsingular_add nonsingular nonsingular
      (fun pair => yDifferent pair.2)
    have afterCurve := (montgomery_equation _ _).mpr afterNonsingular.1
    have rightZero := montgomery_zero_x _ _ afterCurve (xEquation.symm.trans uZero)
    exact leftZero.trans rightZero.symm
  · exact (doubleV_chart _ _ p.onCurve nonzeroX yZero plus minus).trans coordinates.2.symm

theorem toMontgomery_double (p : EPoint) : toMontgomery (p.add p)=toMontgomery p+toMontgomery p := by
  by_cases infinite : p.y=1
  · have identity : p=EPoint.identity := epoint_ext _ _ (edwards_y_one _ _ p.onCurve infinite) infinite
    subst p
    rw [epoint_add_identity,toMontgomery_identity,zero_add]
  by_cases xZero : p.x=0
  · have same : p.neg=p := by
      apply epoint_ext
      · simp only [EPoint.neg,xZero,neg_zero]
      · rfl
    have added : p.add p=EPoint.identity :=
      (congrArg p.add same.symm).trans (epoint_add_neg p)
    have opposite : -toMontgomery p=toMontgomery p := by rw [←toMontgomery_neg,same]
    rw [added,toMontgomery_identity]
    exact (show toMontgomery p+toMontgomery p=0 from by simpa only [opposite] using add_neg_cancel (toMontgomery p)).symm
  · exact toMontgomery_double_regular p xZero infinite

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.regular_plus_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjub.regular_v_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjub.regular_v_not_neg
#print axioms LeanCrypto.Proofs.BabyJubjub.double_math_slope
#print axioms LeanCrypto.Proofs.BabyJubjub.double_math_coordinates
#print axioms LeanCrypto.Proofs.BabyJubjub.montgomery_zero_x
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_double_regular
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_double
