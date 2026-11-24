import LeanCryptoProofs.BabyJubjub.DoublePolynomial

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace LeanCrypto.Proofs.BabyJubjub

def doubleSlope (x y : Field) : Field :=
  (3*(chartU y)^2+337396*chartU y+1)/(2*chartV x y)
def doubleU (x y : Field) : Field := (doubleSlope x y)^2-168698-2*chartU y
def doubleV (x y : Field) : Field := doubleSlope x y*(chartU y-doubleU x y)-chartV x y

theorem edwards_coefficient_nonzero (x y : Field) (equation : Edwards x y) :
    168700-168696*y^2≠0 := by
  intro zero
  unfold Edwards at equation
  have square : y^2=1 := by linear_combination equation-x^2*zero
  have impossible : (4:Field)=0 := by linear_combination zero+168696*square
  exact (by decide +kernel : (4:Field)≠0) impossible

theorem double_difference_nonzero (x y : Field) (equation : Edwards x y) (nonzero : x≠0) :
    doubleM x y-doubleB x y≠0 := by
  have identity : doubleM x y-doubleB x y=2*x^2*(168700-168696*y^2) := by
    unfold doubleM doubleB
    unfold Edwards at equation
    linear_combination -equation
  rw [identity]
  exact mul_ne_zero (mul_ne_zero (by decide +kernel) (pow_ne_zero 2 nonzero))
    (edwards_coefficient_nonzero x y equation)

theorem fraction_chartU (m b : Field) (nonzero : m≠0) (difference : m-b≠0) :
    chartU (b/m)=(m+b)/(m-b) := by
  unfold chartU
  field_simp [nonzero,difference]

theorem doubleU_fraction (x y : Field) (plus : 1+y≠0) (minus : 1-y≠0) :
    doubleU x y=doubleN x y/doubleD y := by
  unfold doubleU doubleSlope chartV chartU doubleN doubleD doubleC
  field_simp [plus,minus,show (2:Field)≠0 from by decide +kernel,
    show (4:Field)≠0 from by decide +kernel,show (8:Field)≠0 from by decide +kernel]
  norm_num
  ring

theorem doubleV_fraction (x y : Field) (nonzeroX : x≠0) (plus : 1+y≠0) (minus : 1-y≠0) :
    doubleV x y=doubleVN x y/doubleVD x y := by
  unfold doubleV doubleU doubleSlope chartV chartU doubleVN doubleVD doubleN doubleD doubleC
  field_simp [nonzeroX,plus,minus,show (2:Field)≠0 from by decide +kernel,
    show (4:Field)≠0 from by decide +kernel,show (8:Field)≠0 from by decide +kernel]
  norm_num
  ring

theorem doubleY_finite (x y : Field) (equation : Edwards x y) (nonzero : x≠0) :
    edwardsAddY x y x y≠1 := by
  have denominators := BabyJubjubComplete.babyjub_complete_denominators x y x y equation equation
  have difference := double_difference_nonzero x y equation nonzero
  intro one
  have doubled : edwardsAddY x y x y=doubleB x y/doubleM x y := by
    unfold edwardsAddY doubleB doubleM
    congr 2 <;> ring
  rw [doubled] at one
  have equal : doubleB x y=doubleM x y := (div_eq_one_iff_eq (by
    simpa only [doubleM,pow_two,mul_assoc] using denominators.2)).1 one
  exact difference (sub_eq_zero.mpr equal.symm)

theorem doubleU_chart (x y : Field) (equation : Edwards x y) (nonzeroX : x≠0)
    (plus : 1+y≠0) (minus : 1-y≠0) :
    chartU (edwardsAddY x y x y)=doubleU x y := by
  have denominators := BabyJubjubComplete.babyjub_complete_denominators x y x y equation equation
  have negative : doubleM x y≠0 := by
    simpa only [doubleM,pow_two,mul_assoc] using denominators.2
  have difference := double_difference_nonzero x y equation nonzeroX
  have denominator : doubleD y≠0 := by
    unfold doubleD
    exact mul_ne_zero (mul_ne_zero (by decide +kernel) (pow_ne_zero 2 plus)) (pow_ne_zero 2 minus)
  have polynomial := double_u_polynomial x y equation
  calc
    chartU (edwardsAddY x y x y)=chartU (doubleB x y/doubleM x y) := by
      congr 1
      unfold edwardsAddY doubleB doubleM
      congr 2 <;> ring
    _=(doubleM x y+doubleB x y)/(doubleM x y-doubleB x y) := fraction_chartU _ _ negative difference
    _=doubleN x y/doubleD y := (div_eq_div_iff difference denominator).2 (sub_eq_zero.mp polynomial)
    _=doubleU x y := (doubleU_fraction x y plus minus).symm

theorem doubleV_chart (x y : Field) (equation : Edwards x y) (nonzeroX : x≠0)
    (nonzeroY : y≠0) (plus : 1+y≠0) (minus : 1-y≠0) :
    chartV (edwardsAddX x y x y) (edwardsAddY x y x y)=doubleV x y := by
  have denominators := BabyJubjubComplete.babyjub_complete_denominators x y x y equation equation
  have positive : 1+168696*x^2*y^2≠0 := by
    simpa only [pow_two,mul_assoc] using denominators.1
  have negative : doubleM x y≠0 := by
    simpa only [doubleM,pow_two,mul_assoc] using denominators.2
  have difference := double_difference_nonzero x y equation nonzeroX
  have four : (4:Field)≠0 := by decide +kernel
  have two : (2:Field)≠0 := by decide +kernel
  have dNonzero : doubleD y≠0 :=
    mul_ne_zero (mul_ne_zero four (pow_ne_zero 2 plus)) (pow_ne_zero 2 minus)
  have vNonzero : doubleVD x y≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two plus) (pow_ne_zero 2 minus)) dNonzero) nonzeroX
  have leftNonzero : (doubleM x y-doubleB x y)*2*x*y≠0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero difference two) nonzeroX) nonzeroY
  have doubled : edwardsAddY x y x y=doubleB x y/doubleM x y := by
    unfold edwardsAddY doubleB doubleM
    congr 2 <;> ring
  have polynomial := double_v_polynomial x y equation
  calc
    chartV (edwardsAddX x y x y) (edwardsAddY x y x y)=
        (doubleM x y+doubleB x y)*(1+168696*x^2*y^2)/((doubleM x y-doubleB x y)*2*x*y) := by
      unfold chartV
      rw [doubled,fraction_chartU _ _ negative difference]
      unfold edwardsAddX
      field_simp [positive,difference,nonzeroX,nonzeroY,two]
      have half : (2:Field)⁻¹*2=1 := inv_mul_cancel₀ two
      linear_combination (doubleM x y+doubleB x y)*(1+168696*x^2*y^2)*half
    _=doubleVN x y/doubleVD x y :=
      (div_eq_div_iff leftNonzero vNonzero).2 (sub_eq_zero.mp polynomial)
    _=doubleV x y := (doubleV_fraction x y nonzeroX plus minus).symm

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.edwards_coefficient_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjub.double_difference_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjub.fraction_chartU
#print axioms LeanCrypto.Proofs.BabyJubjub.doubleU_fraction
#print axioms LeanCrypto.Proofs.BabyJubjub.doubleV_fraction
#print axioms LeanCrypto.Proofs.BabyJubjub.doubleY_finite
#print axioms LeanCrypto.Proofs.BabyJubjub.doubleU_chart
#print axioms LeanCrypto.Proofs.BabyJubjub.doubleV_chart
