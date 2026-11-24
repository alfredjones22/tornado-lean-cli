import LeanCryptoProofs.BabyJubjub.EdwardsAddition

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace LeanCrypto.Proofs.BabyJubjub

structure EPoint where
  x : Field
  y : Field
  onCurve : Edwards x y

def chartU (y : Field) : Field := (1+y)/(1-y)
def chartV (x y : Field) : Field := chartU y/x

theorem montgomery_equation (u v : Field) : Montgomery u v ↔ curve.Equation u v := by
  simp only [Montgomery,WeierstrassCurve.Affine.equation_iff,curve,zero_mul,add_zero,one_mul]

theorem edwards_x_zero (x y : Field) (equation : Edwards x y) (zero : x=0) :
    y=1 ∨ y= -1 := by
  have square : y^2=1 := by simpa only [Edwards,zero,zero_pow (by decide : 2≠0),mul_zero,zero_mul,zero_add,add_zero] using equation
  exact sq_eq_one_iff.mp square

theorem chart_curve_regular (x y : Field) (equation : Edwards x y)
    (nonzeroX : x≠0) (nonzeroY : 1-y≠0) : Montgomery (chartU y) (chartV x y) := by
  unfold Montgomery chartV chartU
  field_simp [nonzeroX,nonzeroY]
  unfold Edwards at equation
  linear_combination -(1+y)*equation

theorem chart_curve (x y : Field) (equation : Edwards x y) (finite : y≠1) :
    Montgomery (chartU y) (chartV x y) := by
  by_cases nonzero : x=0
  · rcases edwards_x_zero x y equation nonzero with one | neg
    · exact False.elim (finite one)
    · simp only [nonzero,neg,chartU,chartV,add_neg_cancel,zero_div,zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),mul_zero,add_zero,Montgomery]
  · exact chart_curve_regular x y equation nonzero (sub_ne_zero.mpr finite.symm)

noncomputable def toMontgomery (point : EPoint) : Point :=
  if finite : point.y=1 then 0
  else WeierstrassCurve.Affine.Point.mk ((montgomery_equation _ _).mp (chart_curve _ _ point.onCurve finite))

def EPoint.identity : EPoint := ⟨0,1,by norm_num [Edwards]⟩
def EPoint.add (p q : EPoint) : EPoint :=
  ⟨edwardsAddX p.x p.y q.x q.y,edwardsAddY p.x p.y q.x q.y,edwards_add_curve _ _ _ _ p.onCurve q.onCurve⟩
def EPoint.neg (p : EPoint) : EPoint := ⟨-p.x,p.y,by simpa only [Edwards,neg_sq] using p.onCurve⟩

theorem toMontgomery_identity : toMontgomery EPoint.identity=0 := by
  simp only [toMontgomery,EPoint.identity,↓reduceDIte]

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.montgomery_equation
#print axioms LeanCrypto.Proofs.BabyJubjub.edwards_x_zero
#print axioms LeanCrypto.Proofs.BabyJubjub.chart_curve_regular
#print axioms LeanCrypto.Proofs.BabyJubjub.chart_curve
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_identity
