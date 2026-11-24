import LeanCryptoProofs.BabyJubjub.TorsionGroup
import LeanCryptoProofs.BabyJubjub.ChartV

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BabyJubjubCharts

theorem toMontgomery_add_regular (p q : EPoint)
    (nonzeroP : p.x≠0) (nonzeroQ : q.x≠0) (finiteP : p.y≠1) (finiteQ : q.y≠1)
    (different : chartU p.y≠chartU q.y) :
    toMontgomery (p.add q)=toMontgomery p+toMontgomery q := by
  have pChart : 1-p.y≠0 := sub_ne_zero.mpr finiteP.symm
  have qChart : 1-q.y≠0 := sub_ne_zero.mpr finiteQ.symm
  have afterChart := regular_output_chart_nonzero p.x p.y q.x q.y p.onCurve q.onCurve
    nonzeroP nonzeroQ pChart qChart different
  have finiteAfter : (p.add q).y≠1 := by
    intro infinite
    apply afterChart
    change 1-(p.add q).y=0
    rw [infinite,sub_self]
  have pEquation := (montgomery_equation _ _).mp (chart_curve _ _ p.onCurve finiteP)
  have qEquation := (montgomery_equation _ _).mp (chart_curve _ _ q.onCurve finiteQ)
  let pNonsingular : curve.Nonsingular (chartU p.y) (chartV p.x p.y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp pEquation
  let qNonsingular : curve.Nonsingular (chartU q.y) (chartV q.x q.y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp qEquation
  have pSource : toMontgomery p=WeierstrassCurve.Affine.Point.some (chartU p.y) (chartV p.x p.y) pNonsingular := by
    simp only [toMontgomery,finiteP,↓reduceDIte,WeierstrassCurve.Affine.Point.mk]
  have qSource : toMontgomery q=WeierstrassCurve.Affine.Point.some (chartU q.y) (chartV q.x q.y) qNonsingular := by
    simp only [toMontgomery,finiteQ,↓reduceDIte,WeierstrassCurve.Affine.Point.mk]
  have addition := WeierstrassCurve.Affine.Point.add_of_X_ne (h₁:=pNonsingular) (h₂:=qNonsingular) different
  rw [pSource,qSource,addition,toMontgomery,dif_neg finiteAfter]
  simp only [WeierstrassCurve.Affine.Point.mk,WeierstrassCurve.Affine.Point.some.injEq]
  have xEquation := chart_addX_regular p.x p.y q.x q.y p.onCurve q.onCurve
    nonzeroP nonzeroQ pChart qChart different
  refine ⟨xEquation,?_⟩
  by_cases xZero : edwardsAddX p.x p.y q.x q.y=0
  · have afterCurve := edwards_add_curve _ _ _ _ p.onCurve q.onCurve
    have yNegative : edwardsAddY p.x p.y q.x q.y= -1 :=
      (edwards_x_zero _ _ afterCurve xZero).resolve_left finiteAfter
    have uZero : chartU (edwardsAddY p.x p.y q.x q.y)=0 :=
      by simp only [yNegative,chartU,add_neg_cancel,zero_div]
    have leftZero : chartV (edwardsAddX p.x p.y q.x q.y) (edwardsAddY p.x p.y q.x q.y)=0 := by
      unfold chartV
      rw [uZero,zero_div]
    have afterNonsingular := WeierstrassCurve.Affine.nonsingular_add pNonsingular qNonsingular
      (fun pair => different pair.1)
    have rightCurve := (montgomery_equation _ _).mpr afterNonsingular.1
    have rightZero := montgomery_zero_x _ _ rightCurve (xEquation.symm.trans uZero)
    exact leftZero.trans rightZero.symm
  · exact chart_addY_regular p.x p.y q.x q.y p.onCurve q.onCurve
      nonzeroP nonzeroQ pChart qChart different xZero

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_add_regular
