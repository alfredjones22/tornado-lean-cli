import LeanCryptoProofs.BabyJubjub.EdwardsPoint

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub

theorem epoint_ext (p q : EPoint) (x : p.x=q.x) (y : p.y=q.y) : p=q := by
  cases p
  cases q
  cases x
  cases y
  rfl

theorem edwards_y_one (x y : Field) (equation : Edwards x y) (one : y=1) : x=0 := by
  have coefficient : (4:Field)≠0 := by decide +kernel
  have square : (4:Field)*x^2=0 := by
    unfold Edwards at equation
    rw [one] at equation
    linear_combination equation
  exact (pow_eq_zero_iff (by decide : 2≠0)).mp ((mul_eq_zero.mp square).resolve_left coefficient)

theorem edwards_y_neg_one (x y : Field) (equation : Edwards x y) (one : y= -1) : x=0 := by
  have altered : Edwards x (-y) := by simpa only [Edwards,neg_sq] using equation
  apply edwards_y_one x (-y) altered
  simp only [one,neg_neg]

theorem epoint_add_identity (p : EPoint) : p.add EPoint.identity=p := by
  apply epoint_ext
  · simp [EPoint.add,EPoint.identity,edwardsAddX]
  · simp [EPoint.add,EPoint.identity,edwardsAddY]

theorem epoint_identity_add (p : EPoint) : EPoint.identity.add p=p := by
  apply epoint_ext
  · simp [EPoint.add,EPoint.identity,edwardsAddX]
  · simp [EPoint.add,EPoint.identity,edwardsAddY]

theorem epoint_add_comm (p q : EPoint) : p.add q=q.add p := by
  apply epoint_ext <;> dsimp only [EPoint.add,edwardsAddX,edwardsAddY] <;> congr 1 <;> ring

theorem epoint_add_neg (p : EPoint) : p.add p.neg=EPoint.identity := by
  have denominators := BabyJubjubComplete.babyjub_complete_denominators p.x p.y (-p.x) p.y
    p.onCurve p.neg.onCurve
  apply epoint_ext
  · simp only [EPoint.add,EPoint.neg,EPoint.identity,edwardsAddX]
    have numerator : p.x*p.y+p.y*(-p.x)=0 := by ring
    rw [numerator,zero_div]
  · change edwardsAddY p.x p.y (-p.x) p.y=1
    unfold edwardsAddY
    apply (div_eq_one_iff_eq denominators.2).2
    have equation := p.onCurve
    unfold Edwards at equation
    linear_combination equation

theorem toMontgomery_neg (p : EPoint) : toMontgomery p.neg= -toMontgomery p := by
  by_cases infinite : p.y=1
  · simp only [toMontgomery,EPoint.neg,infinite,↓reduceDIte,neg_zero]
  · simp only [toMontgomery,EPoint.neg,infinite,↓reduceDIte]
    simp only [WeierstrassCurve.Affine.Point.mk,chartV,div_neg_eq_neg_div]
    change WeierstrassCurve.Affine.Point.some (chartU p.y) (-(chartU p.y/p.x)) _ =
      WeierstrassCurve.Affine.Point.neg (WeierstrassCurve.Affine.Point.some (chartU p.y) (chartU p.y/p.x) _)
    simp only [WeierstrassCurve.Affine.Point.neg,WeierstrassCurve.Affine.negY,curve,zero_mul,sub_zero]


end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.epoint_ext
#print axioms LeanCrypto.Proofs.BabyJubjub.edwards_y_one
#print axioms LeanCrypto.Proofs.BabyJubjub.edwards_y_neg_one
#print axioms LeanCrypto.Proofs.BabyJubjub.epoint_add_identity
#print axioms LeanCrypto.Proofs.BabyJubjub.epoint_identity_add
#print axioms LeanCrypto.Proofs.BabyJubjub.epoint_add_comm
#print axioms LeanCrypto.Proofs.BabyJubjub.epoint_add_neg
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_neg
