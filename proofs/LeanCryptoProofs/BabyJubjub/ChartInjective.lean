import LeanCryptoProofs.BabyJubjub.TorsionGroup
import LeanCryptoProofs.BabyJubjub.NativeGroupPoint

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub

theorem toMontgomery_injective : Function.Injective toMontgomery := by
  intro p q equal
  by_cases infiniteP : p.y=1
  · have zeroP : toMontgomery p=0 := (toMontgomery_zero_iff p).mpr infiniteP
    have infiniteQ : q.y=1 := (toMontgomery_zero_iff q).mp (equal.symm.trans zeroP)
    exact epoint_ext p q
      ((edwards_y_one _ _ p.onCurve infiniteP).trans (edwards_y_one _ _ q.onCurve infiniteQ).symm)
      (infiniteP.trans infiniteQ.symm)
  have infiniteQ : q.y≠1 := by
    intro infinite
    have zeroQ : toMontgomery q=0 := (toMontgomery_zero_iff q).mpr infinite
    exact infiniteP ((toMontgomery_zero_iff p).mp (equal.trans zeroQ))
  rw [toMontgomery,dif_neg infiniteP,toMontgomery,dif_neg infiniteQ] at equal
  simp only [WeierstrassCurve.Affine.Point.mk,WeierstrassCurve.Affine.Point.some.injEq] at equal
  have yEqual := chartU_injective _ _ infiniteP infiniteQ equal.1
  by_cases zeroQ : q.x=0
  · have yNeg := (edwards_x_zero _ _ q.onCurve zeroQ).resolve_left infiniteQ
    have zeroP := edwards_y_neg_one _ _ p.onCurve (yEqual.trans yNeg)
    exact epoint_ext _ _ (zeroP.trans zeroQ.symm) yEqual
  rcases epoint_eq_or_neg_of_chartU p q infiniteP infiniteQ equal.1 with same | opposite
  · exact same
  · have nonzero := mul_ne_zero (by decide +kernel : (2:Field)≠0)
      (regular_v_nonzero q zeroQ infiniteQ)
    rw [opposite] at equal
    simp only [EPoint.neg,chartV,div_neg_eq_neg_div] at equal
    unfold chartV at nonzero
    exact False.elim (nonzero (by linear_combination -equal.2))

theorem groupPoint_eq_normalized (p q : RawPoint) (first : Admissible p) (second : Admissible q) :
    groupPoint p=groupPoint q ↔ normalizedX p=normalizedX q ∧ normalizedY p=normalizedY q := by
  rw [groupPoint_admitted p first,groupPoint_admitted q second]
  constructor
  · intro equal
    have points := toMontgomery_injective equal
    exact ⟨congrArg EPoint.x points,congrArg EPoint.y points⟩
  · rintro ⟨x,y⟩
    exact congrArg toMontgomery (epoint_ext _ _ x y)

theorem native_affine_eq_of_groupPoint (p q : RawPoint) (first : Admissible p) (second : Admissible q)
    (equal : groupPoint p=groupPoint q) : nativeAffine p=nativeAffine q := by
  obtain ⟨x,y⟩ := (groupPoint_eq_normalized p q first second).mp equal
  rw [native_affine_construct p first,native_affine_construct q second,x,y]

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_injective
#print axioms LeanCrypto.Proofs.BabyJubjub.groupPoint_eq_normalized
#print axioms LeanCrypto.Proofs.BabyJubjub.native_affine_eq_of_groupPoint
