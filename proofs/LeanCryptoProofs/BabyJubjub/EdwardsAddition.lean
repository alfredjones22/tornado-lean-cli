import LeanCryptoProofs.BabyJubjub.Montgomery
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace LeanCrypto.Proofs.BabyJubjub

def edwardsAddX (x y z w : Field) : Field := (x*w+y*z)/(1+168696*x*z*y*w)
def edwardsAddY (x y z w : Field) : Field := (y*w-168700*x*z)/(1-168696*x*z*y*w)

theorem edwards_add_polynomial (x y z w : Field) (first : Edwards x y) (second : Edwards z w) :
    168700*(x*w+y*z)^2*(1-168696*x*z*y*w)^2+
      (y*w-168700*x*z)^2*(1+168696*x*z*y*w)^2-
      (1-(168696*x*z*y*w)^2)^2-
      168696*(x*w+y*z)^2*(y*w-168700*x*z)^2=0 := by
  unfold Edwards at first second
  linear_combination ((4800808194817536 : Field)*x^2*y^2*z^4*w^4+(4800922028179200 : Field)*x^2*z^4*w^4+(-4801035864240000 : Field)*x^2*z^4*w^2+(-28459015200 : Field)*x^2*z^2*w^4+(28458340416 : Field)*y^2*z^4*w^4+(-28459015200 : Field)*y^2*z^4*w^2+(-168696 : Field)*y^2*z^2*w^4+(28459689984 : Field)*z^4*w^4+(-56919380000 : Field)*z^4*w^2+(28459690000 : Field)*z^4+(-337400 : Field)*z^2*w^4+(337408 : Field)*z^2*w^2+(1 : Field)*w^4)*first+((4801035864240000 : Field)*x^4*z^2*w^2+(1349600 : Field)*x^2*z^2*w^2+(-28459690000 : Field)*x^2*z^2+(-168700 : Field)*x^2*w^2+(168696 : Field)*y^4*z^2*w^2+(8 : Field)*y^2*z^2*w^2+(-168700 : Field)*y^2*z^2+(-1 : Field)*y^2*w^2+(-168704 : Field)*z^2*w^2+(168700 : Field)*z^2+(1 : Field)*w^2+(1 : Field))*second

theorem edwards_fraction_curve (u v plus minus : Field) (positive : plus≠0) (negative : minus≠0)
    (identity : 168700*u^2*minus^2+v^2*plus^2-plus^2*minus^2-168696*u^2*v^2=0) :
    Edwards (u/plus) (v/minus) := by
  unfold Edwards
  field_simp [positive,negative]
  linear_combination identity

theorem edwards_add_curve (x y z w : Field) (first : Edwards x y) (second : Edwards z w) :
    Edwards (edwardsAddX x y z w) (edwardsAddY x y z w) := by
  have nonzero := BabyJubjubComplete.babyjub_complete_denominators x y z w first second
  have polynomial := edwards_add_polynomial x y z w first second
  apply edwards_fraction_curve _ _ _ _ nonzero.1 nonzero.2
  linear_combination polynomial

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.edwards_add_polynomial
#print axioms LeanCrypto.Proofs.BabyJubjub.edwards_fraction_curve
#print axioms LeanCrypto.Proofs.BabyJubjub.edwards_add_curve
