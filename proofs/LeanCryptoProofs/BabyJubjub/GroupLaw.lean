import LeanCryptoProofs.BabyJubjub.RegularGroup
import LeanCryptoProofs.BabyJubjub.NativeGroupPoint

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub

/-- The complete Edwards formula agrees with Mathlib's proved group law,
including infinity, order2, equal/negative points, and every regular pair. -/
theorem toMontgomery_add (p q : EPoint) :
    toMontgomery (p.add q)=toMontgomery p+toMontgomery q := by
  by_cases infiniteP : p.y=1
  · have identity : p=EPoint.identity := epoint_ext _ _ (edwards_y_one _ _ p.onCurve infiniteP) infiniteP
    subst p
    rw [epoint_identity_add,toMontgomery_identity,zero_add]
  by_cases infiniteQ : q.y=1
  · have identity : q=EPoint.identity := epoint_ext _ _ (edwards_y_one _ _ q.onCurve infiniteQ) infiniteQ
    subst q
    rw [epoint_add_identity,toMontgomery_identity,add_zero]
  by_cases pZero : p.x=0
  · have negative := (edwards_x_zero _ _ p.onCurve pZero).resolve_left infiniteP
    have same : p=EPoint.torsionTwo := epoint_ext _ _ pZero negative
    subst p
    calc
      toMontgomery (EPoint.torsionTwo.add q)=toMontgomery (q.add EPoint.torsionTwo) :=
        congrArg toMontgomery (epoint_add_comm _ _)
      _=toMontgomery q+torsionTwo := toMontgomery_add_torsionTwo q
      _=toMontgomery EPoint.torsionTwo+toMontgomery q := by rw [toMontgomery_torsionTwo,add_comm]
  by_cases qZero : q.x=0
  · have negative := (edwards_x_zero _ _ q.onCurve qZero).resolve_left infiniteQ
    have same : q=EPoint.torsionTwo := epoint_ext _ _ qZero negative
    subst q
    simpa only [toMontgomery_torsionTwo] using toMontgomery_add_torsionTwo p
  by_cases sameU : chartU p.y=chartU q.y
  · rcases epoint_eq_or_neg_of_chartU p q infiniteP infiniteQ sameU with same | opposite
    · subst p
      exact toMontgomery_double q
    · calc
        toMontgomery (p.add q)=0 := by
          rw [opposite,epoint_add_comm,epoint_add_neg,toMontgomery_identity]
        _=toMontgomery p+toMontgomery q := by
          rw [opposite,toMontgomery_neg,neg_add_cancel]
  · exact toMontgomery_add_regular p q pZero qZero infiniteP infiniteQ sameU

/-- Exact actual extended-point addition, with all normalization and chart
cases constructed rather than assumed as a final verifier premise. -/
theorem add_groupPoint (p q : RawPoint) (first : Admissible p) (second : Admissible q) :
    groupPoint (nativeAddPoints p q)=groupPoint p+groupPoint q := by
  rw [groupPoint_admitted _ (add_admissible p q first second),
    groupPoint_admitted p first,groupPoint_admitted q second,normalizedPoint_add p q first second]
  exact toMontgomery_add _ _

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_add
#print axioms LeanCrypto.Proofs.BabyJubjub.add_groupPoint
