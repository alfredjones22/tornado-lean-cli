import LeanCryptoProofs.BabyJubjub.EdwardsPoint

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace LeanCrypto.Proofs.BabyJubjub

def doubleC (y : Field) : Field := 3*(1+y)^2+337396*(1+y)*(1-y)+(1-y)^2
def doubleN (x y : Field) : Field := x^2*(doubleC y)^2-674792*(1+y)^2*(1-y)^2-8*(1+y)^3*(1-y)
def doubleD (y : Field) : Field := 4*(1+y)^2*(1-y)^2
def doubleVN (x y : Field) : Field := x^2*doubleC y*((1+y)*doubleD y-doubleN x y*(1-y))-2*(1+y)^2*(1-y)*doubleD y
def doubleVD (x y : Field) : Field := 2*(1+y)*(1-y)^2*doubleD y*x
def doubleB (x y : Field) : Field := y^2-168700*x^2
def doubleM (x y : Field) : Field := 1-168696*x^2*y^2

theorem double_u_polynomial (x y : Field) (equation : Edwards x y) :
    (doubleM x y+doubleB x y)*doubleD y-doubleN x y*(doubleM x y-doubleB x y)=0 := by
  unfold doubleM doubleB doubleD doubleN doubleC
  unfold Edwards at equation
  linear_combination ((-113833361664 : Field)*x^2*y^4+(2699136 : Field)*x^2*y^3+(227672121584 : Field)*x^2*y^2+(-2699200 : Field)*x^2*y+(-113838760000 : Field)*x^2+(-674780 : Field)*y^4+(16 : Field)*y^3+(1349584 : Field)*y^2+(-16 : Field)*y+(-674804 : Field))*equation

theorem double_v_polynomial (x y : Field) (equation : Edwards x y) :
    (doubleM x y+doubleB x y)*(1+168696*x^2*y^2)*doubleVD x y-
      doubleVN x y*((doubleM x y-doubleB x y)*2*x*y)=0 := by
  unfold doubleM doubleB doubleVD doubleVN doubleD doubleN doubleC
  unfold Edwards at equation
  linear_combination ((76812931117080576 : Field)*x^5*y^8+(-76815663117760512 : Field)*x^5*y^7+(-230441525319532032 : Field)*x^5*y^6+(230449721451130240 : Field)*x^5*y^5+(230444257320211328 : Field)*x^5*y^4+(-230452453581369600 : Field)*x^5*y^3+(-76815663117760000 : Field)*x^5*y^2+(76818395248000000 : Field)*x^5*y+(1349568 : Field)*x^3*y^9+(455334796224 : Field)*x^3*y^8+(-455348291872 : Field)*x^3*y^7+(-1366012485984 : Field)*x^3*y^6+(1366044875776 : Field)*x^3*y^5+(1366020583360 : Field)*x^3*y^4+(-1366050274272 : Field)*x^3*y^3+(-455342893600 : Field)*x^3*y^2+(455352340800 : Field)*x^3*y+(16 : Field)*x*y^8+(24 : Field)*x*y^7+(-56 : Field)*x*y^6+(-56 : Field)*x*y^5+(56 : Field)*x*y^4+(40 : Field)*x*y^3+(-8 : Field)*x*y^2+(-8 : Field)*x*y+(-8 : Field)*x)*equation

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.double_u_polynomial
#print axioms LeanCrypto.Proofs.BabyJubjub.double_v_polynomial
