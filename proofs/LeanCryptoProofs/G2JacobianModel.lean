import LeanCryptoProofs.Fp2Model
import Mathlib.Tactic.Ring

/-! Curve preservation for the actual native G2 Jacobian implementation.
This does not identify the operations with an elliptic-curve group law. -/
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanCrypto.Proofs.BN254G2Jacobian

open LeanCrypto.BN254.G2 LeanCrypto.Proofs.BN254Fp2

def ProjectiveEquation (point : Jacobian) : Prop :=
  model point.y ^ 2 = model point.x ^ 3 + model twistB * model point.z ^ 6

/-- Native infinity is a distinguished sentinel `(0,1,0)` rather than a
homogeneous curve representative. Finite admitted points satisfy the
independent projective equation and have nonzero Z. -/
def Admissible (point : Jacobian) : Prop :=
  point = Jacobian.infinity ∨ (model point.z ≠ 0 ∧ ProjectiveEquation point)

theorem infinity_admissible : Admissible Jacobian.infinity := Or.inl rfl

theorem isInfinity_iff (point : Jacobian) :
    point.isInfinity = true ↔ model point.z = 0 := by
  simpa only [Jacobian.isInfinity, model_zero] using model_beq point.z Fp2.zero

theorem fp_beq_false_iff (left right : Fp2) :
    (left == right) = false ↔ model left ≠ model right := by
  rw [Bool.eq_false_iff]
  exact not_congr (model_beq left right)

theorem admissible_infinity (point : Jacobian) (admitted : Admissible point)
    (infinite : point.isInfinity = true) : point = Jacobian.infinity := by
  rcases admitted with equal | ⟨nonzero, _⟩
  · exact equal
  · exact False.elim (nonzero ((isInfinity_iff point).1 infinite))

theorem ofAffine_admissible (point : Affine) (admitted : point.onCurve = true) :
    Admissible (Jacobian.ofAffine point) := by
  right
  constructor
  · change model Fp2.one ≠ 0
    rw [model_one]
    decide
  · have equation := (affine_onCurve_iff point).1 admitted
    simpa [ProjectiveEquation, Jacobian.ofAffine] using equation

theorem generator_admissible : Admissible (Jacobian.ofAffine generator) := by
  apply ofAffine_admissible
  decide

def doubleX {R : Type} [CommRing R] (x y : R) : R :=
  (3 * x ^ 2) ^ 2 - 2 * (4 * x * y ^ 2)

def doubleY {R : Type} [CommRing R] (x y : R) : R :=
  3 * x ^ 2 * (4 * x * y ^ 2 - doubleX x y) - 8 * y ^ 4

def doubleZ {R : Type} [CommRing R] (y z : R) : R := 2 * y * z

theorem double_polynomial {R : Type} [CommRing R] (x y z coefficient : R)
    (curve : y ^ 2 = x ^ 3 + coefficient * z ^ 6) :
    doubleY x y ^ 2 = doubleX x y ^ 3 + coefficient * doubleZ y z ^ 6 := by
  apply sub_eq_zero.mp
  calc
    doubleY x y ^ 2 - (doubleX x y ^ 3 + coefficient * doubleZ y z ^ 6) =
        64 * y ^ 6 * (y ^ 2 - (x ^ 3 + coefficient * z ^ 6)) := by
      unfold doubleY doubleX doubleZ
      ring
    _ = 0 := by rw [curve]; ring

theorem double_model (point : Jacobian)
    (finite : point.isInfinity = false) (nonzeroY : (point.y == Fp2.zero) = false) :
    model point.double.x = doubleX (model point.x) (model point.y) ∧
    model point.double.y = doubleY (model point.x) (model point.y) ∧
    model point.double.z = doubleZ (model point.y) (model point.z) := by
  simp [Jacobian.double, finite, nonzeroY, doubleX, doubleY, doubleZ]
  constructor
  · ring
  constructor <;> ring

theorem double_infinity : Jacobian.infinity.double = Jacobian.infinity := by
  simp [Jacobian.double, Jacobian.isInfinity, Jacobian.infinity]
  rfl

theorem double_admissible (point : Jacobian) (admitted : Admissible point) :
    Admissible point.double := by
  by_cases infinite : point.isInfinity = true
  · have equal := admissible_infinity point admitted infinite
    subst point
    rw [double_infinity]
    exact infinity_admissible
  have finite : point.isInfinity = false := Bool.eq_false_iff.mpr infinite
  by_cases yZero : (point.y == Fp2.zero) = true
  · left
    simp [Jacobian.double, finite, yZero]
  have nonzeroY : (point.y == Fp2.zero) = false := Bool.eq_false_iff.mpr yZero
  have yNonzero : model point.y ≠ 0 := by
    simpa only [model_zero] using (fp_beq_false_iff point.y Fp2.zero).1 nonzeroY
  have zNonzero : model point.z ≠ 0 := by
    intro zero
    exact infinite ((isInfinity_iff point).2 zero)
  have original : ProjectiveEquation point := by
    rcases admitted with equal | ⟨_, equation⟩
    · subst point
      exact False.elim (zNonzero (by simp [Jacobian.infinity]))
    · exact equation
  have coordinates := double_model point finite nonzeroY
  right
  constructor
  · rw [coordinates.2.2, doubleZ]
    exact mul_ne_zero (mul_ne_zero (by decide) yNonzero) zNonzero
  · unfold ProjectiveEquation at original ⊢
    rw [coordinates.1, coordinates.2.1, coordinates.2.2]
    exact double_polynomial _ _ _ (model twistB) original

def addX {R : Type} [CommRing R] (u v a b : R) : R :=
  (b - a) ^ 2 - (v - u) ^ 3 - 2 * u * (v - u) ^ 2

def addY {R : Type} [CommRing R] (u v a b : R) : R :=
  (b - a) * (u * (v - u) ^ 2 - addX u v a b) - a * (v - u) ^ 3

def addZ {R : Type} [CommRing R] (t u v : R) : R := t * (v - u)

/-- A ring identity for the exact native addition formulas, independent of
the branch condition used to select these formulas. -/
theorem add_polynomial {R : Type} [CommRing R] (u v a b t coefficient : R)
    (first : a ^ 2 = u ^ 3 + coefficient * t ^ 6)
    (second : b ^ 2 = v ^ 3 + coefficient * t ^ 6) :
    addY u v a b ^ 2 = addX u v a b ^ 3 + coefficient * addZ t u v ^ 6 := by
  apply sub_eq_zero.mp
  calc
    addY u v a b ^ 2 - (addX u v a b ^ 3 + coefficient * addZ t u v ^ 6) =
        (v - u) ^ 6 * (a ^ 2 - (u ^ 3 + coefficient * t ^ 6)) +
        ((b - a) ^ 2 * (v - u) ^ 3 - (2 * u + v) * (v - u) ^ 5) *
          ((b ^ 2 - (v ^ 3 + coefficient * t ^ 6)) - (a ^ 2 - (u ^ 3 + coefficient * t ^ 6))) := by
      unfold addY addX addZ
      ring
    _ = 0 := by rw [first, second]; ring

theorem scaled_curve {R : Type} [CommRing R] (x y z other coefficient : R)
    (curve : y ^ 2 = x ^ 3 + coefficient * z ^ 6) :
    (y * other ^ 3) ^ 2 = (x * other ^ 2) ^ 3 + coefficient * (z * other) ^ 6 := by
  calc
    (y * other ^ 3) ^ 2 = y ^ 2 * other ^ 6 := by ring
    _ = (x ^ 3 + coefficient * z ^ 6) * other ^ 6 := by rw [curve]
    _ = (x * other ^ 2) ^ 3 + coefficient * (z * other) ^ 6 := by ring

def nativeU (left right : Jacobian) : Fp2 := left.x.mul (right.z.mul right.z)
def nativeS (left right : Jacobian) : Fp2 := (left.y.mul right.z).mul (right.z.mul right.z)

theorem model_nativeU (left right : Jacobian) :
    model (nativeU left right) = model left.x * model right.z ^ 2 := by
  simp [nativeU, pow_two]

theorem model_nativeS (left right : Jacobian) :
    model (nativeS left right) = model left.y * model right.z ^ 3 := by
  simp [nativeS]
  ring

theorem add_model (left right : Jacobian)
    (leftFinite : left.isInfinity = false) (rightFinite : right.isInfinity = false)
    (distinct : (nativeU left right == nativeU right left) = false) :
    model (left.add right).x = addX (model (nativeU left right)) (model (nativeU right left))
        (model (nativeS left right)) (model (nativeS right left)) ∧
    model (left.add right).y = addY (model (nativeU left right)) (model (nativeU right left))
        (model (nativeS left right)) (model (nativeS right left)) ∧
    model (left.add right).z = addZ (model left.z * model right.z)
        (model (nativeU left right)) (model (nativeU right left)) := by
  change (left.x.mul (right.z.mul right.z) == right.x.mul (left.z.mul left.z)) = false at distinct
  simp [Jacobian.add, leftFinite, rightFinite, distinct, nativeU, nativeS, addX, addY, addZ]
  constructor <;> ring

theorem add_left_infinity (point : Jacobian) :
    Jacobian.infinity.add point = point := by
  simp [Jacobian.add, Jacobian.isInfinity, Jacobian.infinity]
  rfl

theorem add_right_infinity (point : Jacobian) (admitted : Admissible point) :
    point.add Jacobian.infinity = point := by
  by_cases infinite : point.isInfinity = true
  · have equal := admissible_infinity point admitted infinite
    subst point
    exact add_left_infinity Jacobian.infinity
  · have finite : point.isInfinity = false := Bool.eq_false_iff.mpr infinite
    simp only [Jacobian.add, finite,
      show Jacobian.infinity.isInfinity = true from rfl,
      Bool.false_eq_true, ↓reduceIte]
    rfl

theorem add_admissible (left right : Jacobian)
    (leftAdmitted : Admissible left) (rightAdmitted : Admissible right) :
    Admissible (left.add right) := by
  by_cases leftInfinity : left.isInfinity = true
  · have equal := admissible_infinity left leftAdmitted leftInfinity
    subst left
    rw [add_left_infinity]
    exact rightAdmitted
  by_cases rightInfinity : right.isInfinity = true
  · have equal := admissible_infinity right rightAdmitted rightInfinity
    subst right
    rw [add_right_infinity left leftAdmitted]
    exact leftAdmitted
  have leftFinite : left.isInfinity = false := Bool.eq_false_iff.mpr leftInfinity
  have rightFinite : right.isInfinity = false := Bool.eq_false_iff.mpr rightInfinity
  by_cases sameU : (nativeU left right == nativeU right left) = true
  · simp only [nativeU] at sameU
    by_cases sameS : (nativeS left right == nativeS right left) = true
    · simp only [nativeS] at sameS
      have equal : left.add right = left.double := by
        simp [Jacobian.add, leftFinite, rightFinite, sameU, sameS]
      rw [equal]
      exact double_admissible left leftAdmitted
    · have differentS : (nativeS left right == nativeS right left) = false := Bool.eq_false_iff.mpr sameS
      simp only [nativeS] at differentS
      have equal : left.add right = Jacobian.infinity := by
        simp [Jacobian.add, leftFinite, rightFinite, sameU, differentS]
      rw [equal]
      exact infinity_admissible
  have distinct : (nativeU left right == nativeU right left) = false := Bool.eq_false_iff.mpr sameU
  have distinctModels : model (nativeU right left) - model (nativeU left right) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ((fp_beq_false_iff _ _).1 distinct).symm
  have leftNonzero : model left.z ≠ 0 := by
    intro zero
    exact leftInfinity ((isInfinity_iff left).2 zero)
  have rightNonzero : model right.z ≠ 0 := by
    intro zero
    exact rightInfinity ((isInfinity_iff right).2 zero)
  have leftCurve : ProjectiveEquation left := by
    rcases leftAdmitted with equal | ⟨_, equation⟩
    · subst left
      exact False.elim (leftNonzero (by simp [Jacobian.infinity]))
    · exact equation
  have rightCurve : ProjectiveEquation right := by
    rcases rightAdmitted with equal | ⟨_, equation⟩
    · subst right
      exact False.elim (rightNonzero (by simp [Jacobian.infinity]))
    · exact equation
  have coordinates := add_model left right leftFinite rightFinite distinct
  generalize outputEq : left.add right = output at coordinates ⊢
  right
  constructor
  · rw [coordinates.2.2, addZ]
    exact mul_ne_zero (mul_ne_zero leftNonzero rightNonzero) distinctModels
  · unfold ProjectiveEquation at leftCurve rightCurve ⊢
    rw [coordinates.1, coordinates.2.1, coordinates.2.2]
    apply add_polynomial
    · rw [model_nativeU, model_nativeS]
      exact scaled_curve (model left.x) (model left.y) (model left.z) (model right.z) (model twistB) leftCurve
    · rw [model_nativeU, model_nativeS]
      have scaled := scaled_curve (model right.x) (model right.y) (model right.z)
        (model left.z) (model twistB) rightCurve
      rw [mul_comm (model right.z) (model left.z)] at scaled
      exact scaled

end LeanCrypto.Proofs.BN254G2Jacobian

#print axioms LeanCrypto.Proofs.BN254G2Jacobian.infinity_admissible
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.isInfinity_iff
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.fp_beq_false_iff
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.admissible_infinity
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.ofAffine_admissible
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.generator_admissible
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.double_polynomial
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.double_model
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.double_infinity
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.double_admissible
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.add_polynomial
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.scaled_curve
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.model_nativeU
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.model_nativeS
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.add_model
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.add_left_infinity
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.add_right_infinity
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.add_admissible
