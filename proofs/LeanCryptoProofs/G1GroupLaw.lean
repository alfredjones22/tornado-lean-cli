import LeanCryptoProofs.CertifiedFields
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point

/-! Compatibility of the actual native BN254 operations with Mathlib's
proved elliptic-curve group. No point-count or subgroup-order claim. -/
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanCrypto.Proofs.BN254Group

open LeanCrypto.BN254.G1 LeanCrypto.Proofs.BN254Fp LeanCrypto.Proofs.BN254Jacobian
open scoped WeierstrassCurve.Jacobian

abbrev Field := ZMod P

def curve : WeierstrassCurve.Jacobian Field := ⟨0, 0, 0, 0, 3⟩

theorem curve_discriminant : curve.Δ = (-3888 : Field) := by decide +kernel

instance curve_elliptic : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

def coordinates (point : Jacobian) : Fin 3 → Field :=
  ![model point.x, model point.y, model point.z]

/-- Mathlib's normalized affine group point. The native infinity sentinel
has Z=0 and maps to group zero; it is never treated as a nonsingular raw
Jacobian representative. -/
noncomputable def groupPoint (point : Jacobian) : curve.toAffine.Point :=
  WeierstrassCurve.Jacobian.Point.toAffine curve (coordinates point)

theorem native_equation (point : Jacobian) (equation : ProjectiveEquation point) :
    curve.Equation (coordinates point) := by
  simpa [WeierstrassCurve.Jacobian.equation_iff, curve, coordinates, ProjectiveEquation] using sub_eq_zero.mpr equation

theorem native_nonsingular (point : Jacobian) (finite : model point.z ≠ 0)
    (equation : ProjectiveEquation point) : curve.Nonsingular (coordinates point) := by
  have zNonzero : coordinates point 2 ≠ 0 := finite
  apply (WeierstrassCurve.Jacobian.nonsingular_of_Z_ne_zero zNonzero).mpr
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  exact (WeierstrassCurve.Jacobian.equation_of_Z_ne_zero zNonzero).mp
    (native_equation point equation)

theorem infinity_groupPoint : groupPoint Jacobian.infinity = 0 := by
  apply WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero
  simp [coordinates, Jacobian.infinity]

theorem native_double_coordinates (point : Jacobian)
    (finite : point.isInfinity = false) (nonzeroY : (point.y == Fp.zero) = false) :
    coordinates point.double = curve.dblXYZ (coordinates point) := by
  obtain ⟨x, y, z⟩ := double_model point finite nonzeroY
  funext index
  fin_cases index <;>
    simp [coordinates, x, y, z, WeierstrassCurve.Jacobian.dblXYZ,
      WeierstrassCurve.Jacobian.dblX, WeierstrassCurve.Jacobian.dblY,
      WeierstrassCurve.Jacobian.negDblY, WeierstrassCurve.Jacobian.dblZ,
      WeierstrassCurve.Jacobian.negY, WeierstrassCurve.Jacobian.dblU_eq,
      curve, doubleX, doubleY, doubleZ] <;> ring

/-- Actual native doubling agrees with addition in Mathlib's proved group. -/
theorem double_groupPoint (point : Jacobian) (admitted : Admissible point) :
    groupPoint point.double = groupPoint point + groupPoint point := by
  by_cases infinite : point.isInfinity = true
  · have equal := admissible_infinity point admitted infinite
    subst point
    rw [double_infinity, infinity_groupPoint, zero_add]
  have finite : point.isInfinity = false := Bool.eq_false_iff.mpr infinite
  have zNonzero : model point.z ≠ 0 := by
    intro zero
    exact infinite ((isInfinity_iff point).2 zero)
  have equation : ProjectiveEquation point := by
    rcases admitted with equal | ⟨_, equation⟩
    · subst point
      exact False.elim (zNonzero (by simp [Jacobian.infinity]))
    · exact equation
  have nonsingular := native_nonsingular point zNonzero equation
  have addition := WeierstrassCurve.Jacobian.Point.toAffine_add nonsingular nonsingular
  rw [WeierstrassCurve.Jacobian.add_self] at addition
  by_cases yZero : (point.y == Fp.zero) = true
  · have nativeZero : point.double = Jacobian.infinity := by
      simp [Jacobian.double, finite, yZero]
    have modelZero : model point.y = 0 := by
      simpa only [model_zero] using (model_beq point.y Fp.zero).1 yZero
    have resultZero : (curve.dblXYZ (coordinates point)) 2 = 0 := by
      simp [WeierstrassCurve.Jacobian.dblXYZ, WeierstrassCurve.Jacobian.dblZ,
        WeierstrassCurve.Jacobian.negY, curve, coordinates, modelZero]
    rw [nativeZero, infinity_groupPoint]
    rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero resultZero] at addition
    exact addition
  · have nonzeroY : (point.y == Fp.zero) = false := Bool.eq_false_iff.mpr yZero
    change WeierstrassCurve.Jacobian.Point.toAffine curve (coordinates point.double) = _
    rw [native_double_coordinates point finite nonzeroY]
    exact addition

/-- The native addition polynomial is the actual Mathlib Jacobian formula
scaled by the nonzero factor -(Z1*Z2); no group axiom is postulated. -/
theorem add_polynomial_scaled (x1 y1 z1 x2 y2 z2 : Field)
    (first : y1 ^ 2 = x1 ^ 3 + 3 * z1 ^ 6)
    (second : y2 ^ 2 = x2 ^ 3 + 3 * z2 ^ 6) :
    ![addX (x1 * z2 ^ 2) (x2 * z1 ^ 2) (y1 * z2 ^ 3) (y2 * z1 ^ 3),
      addY (x1 * z2 ^ 2) (x2 * z1 ^ 2) (y1 * z2 ^ 3) (y2 * z1 ^ 3),
      addZ (z1 * z2) (x1 * z2 ^ 2) (x2 * z1 ^ 2)] =
      (-(z1 * z2)) • curve.addXYZ ![x1, y1, z1] ![x2, y2, z2] := by
  let u1 := x1 * z2 ^ 2
  let u2 := x2 * z1 ^ 2
  let s1 := y1 * z2 ^ 3
  let s2 := y2 * z1 ^ 3
  let t := z1 * z2
  let v1 : Fin 3 → Field := ![x1, y1, z1]
  let v2 : Fin 3 → Field := ![x2, y2, z2]
  have firstCurve : curve.Equation v1 := by
    simpa [WeierstrassCurve.Jacobian.equation_iff, curve, v1] using sub_eq_zero.mpr first
  have secondCurve : curve.Equation v2 := by
    simpa [WeierstrassCurve.Jacobian.equation_iff, curve, v2] using sub_eq_zero.mpr second
  have mathX : curve.addX v1 v2 * t ^ 2 =
      (s1 - s2) ^ 2 - u1 * (u1 - u2) ^ 2 - u2 * (u1 - u2) ^ 2 := by
    simpa [curve, v1, v2, t, u1, u2, s1, s2, WeierstrassCurve.Jacobian.addZ] using
      WeierstrassCurve.Jacobian.addX_eq' firstCurve secondCurve
  have nativeX : curve.addX v1 v2 * t ^ 2 = addX u1 u2 s1 s2 := by
    rw [mathX]
    unfold addX
    ring
  have mathY : curve.negAddY v1 v2 * t ^ 3 =
      (s1 - s2) * (curve.addX v1 v2 * t ^ 2 - u1 * (u1 - u2) ^ 2) + s1 * (u1 - u2) ^ 3 := by
    simpa [v1, v2, t, u1, u2, s1, s2, WeierstrassCurve.Jacobian.addZ] using
      (WeierstrassCurve.Jacobian.negAddY_eq' (W' := curve) v1 v2)
  have shortY : curve.addY v1 v2 = -curve.negAddY v1 v2 := by
    simp [WeierstrassCurve.Jacobian.addY, WeierstrassCurve.Jacobian.negY, curve]
  have nativeY : (-(t)) ^ 3 * curve.addY v1 v2 = addY u1 u2 s1 s2 := by
    rw [shortY]
    calc
      (-t) ^ 3 * -curve.negAddY v1 v2 = curve.negAddY v1 v2 * t ^ 3 := by ring
      _ = _ := mathY
      _ = addY u1 u2 s1 s2 := by rw [nativeX]; unfold addY; ring
  funext index
  fin_cases index
  · change addX u1 u2 s1 s2 = _
    simpa [WeierstrassCurve.Jacobian.smul_fin3, WeierstrassCurve.Jacobian.addXYZ,
      v1, v2, t, neg_sq, mul_comm] using nativeX.symm
  · change addY u1 u2 s1 s2 = _
    simpa [WeierstrassCurve.Jacobian.smul_fin3, WeierstrassCurve.Jacobian.addXYZ,
      v1, v2, t] using nativeY.symm
  · simp [WeierstrassCurve.Jacobian.smul_fin3, WeierstrassCurve.Jacobian.addXYZ,
      WeierstrassCurve.Jacobian.addZ, addZ]
    ring

theorem native_add_coordinates (left right : Jacobian)
    (leftFinite : left.isInfinity = false) (rightFinite : right.isInfinity = false)
    (distinct : (nativeU left right == nativeU right left) = false)
    (leftCurve : ProjectiveEquation left) (rightCurve : ProjectiveEquation right) :
    coordinates (left.add right) = (-(model left.z * model right.z)) •
      curve.addXYZ (coordinates left) (coordinates right) := by
  obtain ⟨x, y, z⟩ := add_model left right leftFinite rightFinite distinct
  simp only [model_nativeU, model_nativeS] at x y z
  calc
    coordinates (left.add right) =
        ![addX (model left.x * model right.z ^ 2) (model right.x * model left.z ^ 2)
            (model left.y * model right.z ^ 3) (model right.y * model left.z ^ 3),
          addY (model left.x * model right.z ^ 2) (model right.x * model left.z ^ 2)
            (model left.y * model right.z ^ 3) (model right.y * model left.z ^ 3),
          addZ (model left.z * model right.z) (model left.x * model right.z ^ 2)
            (model right.x * model left.z ^ 2)] := by
      funext index
      fin_cases index
      · exact x
      · exact y
      · exact z
    _ = _ := add_polynomial_scaled _ _ _ _ _ _ leftCurve rightCurve

/-- Actual native addition agrees with the established Mathlib group law
for every pair of admitted native representatives, including infinity and
equal/opposite-point branches. -/
theorem add_groupPoint (left right : Jacobian)
    (leftAdmitted : Admissible left) (rightAdmitted : Admissible right) :
    groupPoint (left.add right) = groupPoint left + groupPoint right := by
  by_cases leftInfinity : left.isInfinity = true
  · have equal := admissible_infinity left leftAdmitted leftInfinity
    subst left
    rw [add_left_infinity, infinity_groupPoint, zero_add]
  by_cases rightInfinity : right.isInfinity = true
  · have equal := admissible_infinity right rightAdmitted rightInfinity
    subst right
    rw [add_right_infinity left leftAdmitted, infinity_groupPoint, add_zero]
  have leftFinite : left.isInfinity = false := Bool.eq_false_iff.mpr leftInfinity
  have rightFinite : right.isInfinity = false := Bool.eq_false_iff.mpr rightInfinity
  have leftZ : model left.z ≠ 0 := fun zero => leftInfinity ((isInfinity_iff left).2 zero)
  have rightZ : model right.z ≠ 0 := fun zero => rightInfinity ((isInfinity_iff right).2 zero)
  have leftCurve : ProjectiveEquation left := by
    rcases leftAdmitted with equal | ⟨_, equation⟩
    · subst left
      exact False.elim (leftZ (by simp [Jacobian.infinity]))
    · exact equation
  have rightCurve : ProjectiveEquation right := by
    rcases rightAdmitted with equal | ⟨_, equation⟩
    · subst right
      exact False.elim (rightZ (by simp [Jacobian.infinity]))
    · exact equation
  have leftNonsingular := native_nonsingular left leftZ leftCurve
  have rightNonsingular := native_nonsingular right rightZ rightCurve
  have addition := WeierstrassCurve.Jacobian.Point.toAffine_add leftNonsingular rightNonsingular
  by_cases sameU : (nativeU left right == nativeU right left) = true
  · have xEqual : coordinates left 0 * coordinates right 2 ^ 2 =
        coordinates right 0 * coordinates left 2 ^ 2 := by
      simpa only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_two, model_nativeU] using
        (model_beq (nativeU left right) (nativeU right left)).1 sameU
    by_cases sameS : (nativeS left right == nativeS right left) = true
    · have yEqual : coordinates left 1 * coordinates right 2 ^ 3 =
          coordinates right 1 * coordinates left 2 ^ 3 := by
        simpa only [coordinates, Matrix.cons_val_one, Matrix.cons_val_two, model_nativeS] using
          (model_beq (nativeS left right) (nativeS right left)).1 sameS
      have equivalent := WeierstrassCurve.Jacobian.equiv_of_X_eq_of_Y_eq leftZ rightZ xEqual yEqual
      have samePoint : groupPoint left = groupPoint right :=
        WeierstrassCurve.Jacobian.Point.toAffine_of_equiv equivalent
      have nativeEqual : left.add right = left.double := by
        simp only [nativeU] at sameU
        simp only [nativeS] at sameS
        simp [Jacobian.add, leftFinite, rightFinite, sameU, sameS]
      rw [nativeEqual, double_groupPoint left leftAdmitted, samePoint]
    · have yDistinct : coordinates left 1 * coordinates right 2 ^ 3 ≠
          coordinates right 1 * coordinates left 2 ^ 3 := by
        have nativeDifferent := (fp_beq_false_iff (nativeS left right) (nativeS right left)).1
          (Bool.eq_false_iff.mpr sameS)
        simpa only [coordinates, Matrix.cons_val_one, Matrix.cons_val_two, model_nativeS] using nativeDifferent
      have notEquivalent := WeierstrassCurve.Jacobian.not_equiv_of_Y_ne yDistinct
      rw [WeierstrassCurve.Jacobian.add_of_not_equiv notEquivalent] at addition
      have zeroZ : (curve.addXYZ (coordinates left) (coordinates right)) 2 = 0 := by
        change coordinates left 0 * coordinates right 2 ^ 2 -
          coordinates right 0 * coordinates left 2 ^ 2 = 0
        exact sub_eq_zero.mpr xEqual
      rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_eq_zero zeroZ] at addition
      have nativeEqual : left.add right = Jacobian.infinity := by
        have differentS := Bool.eq_false_iff.mpr sameS
        simp only [nativeU] at sameU
        simp only [nativeS] at differentS
        simp [Jacobian.add, leftFinite, rightFinite, sameU, differentS]
      rw [nativeEqual, infinity_groupPoint]
      exact addition
  · have distinct := Bool.eq_false_iff.mpr sameU
    have xDistinct : coordinates left 0 * coordinates right 2 ^ 2 ≠
        coordinates right 0 * coordinates left 2 ^ 2 := by
      have nativeDifferent := (fp_beq_false_iff (nativeU left right) (nativeU right left)).1 distinct
      simpa only [coordinates, Matrix.cons_val_zero, Matrix.cons_val_two, model_nativeU] using nativeDifferent
    have notEquivalent := WeierstrassCurve.Jacobian.not_equiv_of_X_ne xDistinct
    rw [WeierstrassCurve.Jacobian.add_of_not_equiv notEquivalent] at addition
    change WeierstrassCurve.Jacobian.Point.toAffine curve (coordinates (left.add right)) = _
    rw [native_add_coordinates left right leftFinite rightFinite distinct leftCurve rightCurve,
      WeierstrassCurve.Jacobian.Point.toAffine_smul _
        (Ne.isUnit (neg_ne_zero.mpr (mul_ne_zero leftZ rightZ)))]
    exact addition

/-- Commutativity is inherited from the actual Mathlib group, modulo the
native Jacobian coordinate representation. -/
theorem add_comm_groupPoint (left right : Jacobian)
    (leftAdmitted : Admissible left) (rightAdmitted : Admissible right) :
    groupPoint (left.add right) = groupPoint (right.add left) := by
  rw [add_groupPoint left right leftAdmitted rightAdmitted,
    add_groupPoint right left rightAdmitted leftAdmitted, add_comm]

/-- Associativity is a consequence of the established group operation,
not an additional native-coordinate axiom. -/
theorem add_assoc_groupPoint (a b c : Jacobian)
    (aAdmitted : Admissible a) (bAdmitted : Admissible b) (cAdmitted : Admissible c) :
    groupPoint ((a.add b).add c) = groupPoint (a.add (b.add c)) := by
  rw [add_groupPoint (a.add b) c
      (add_preserves_curve_certified a b aAdmitted bAdmitted) cAdmitted,
    add_groupPoint a b aAdmitted bAdmitted,
    add_groupPoint a (b.add c) aAdmitted
      (add_preserves_curve_certified b c bAdmitted cAdmitted),
    add_groupPoint b c bAdmitted cAdmitted, add_assoc]

/-- The group model maps precisely the admitted native infinity sentinel
to zero; finite curve points do not collapse to the identity. -/
theorem groupPoint_zero_iff (point : Jacobian) (admitted : Admissible point) :
    groupPoint point = 0 ↔ point = Jacobian.infinity := by
  constructor
  · intro zero
    rcases admitted with infinite | ⟨finite, equation⟩
    · exact infinite
    · have nonzero : groupPoint point ≠ 0 := by
        unfold groupPoint
        rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero
          (native_nonsingular point finite equation) finite]
        exact WeierstrassCurve.Affine.Point.some_ne_zero _
      exact False.elim (nonzero zero)
  · intro infinite
    subst point
    exact infinity_groupPoint

end LeanCrypto.Proofs.BN254Group

#print axioms LeanCrypto.Proofs.BN254Group.native_equation
#print axioms LeanCrypto.Proofs.BN254Group.native_nonsingular
#print axioms LeanCrypto.Proofs.BN254Group.infinity_groupPoint
#print axioms LeanCrypto.Proofs.BN254Group.native_double_coordinates

#print axioms LeanCrypto.Proofs.BN254Group.double_groupPoint

#print axioms LeanCrypto.Proofs.BN254Group.add_polynomial_scaled
#print axioms LeanCrypto.Proofs.BN254Group.native_add_coordinates

#print axioms LeanCrypto.Proofs.BN254Group.add_groupPoint

#print axioms LeanCrypto.Proofs.BN254Group.curve_discriminant

#print axioms LeanCrypto.Proofs.BN254Group.add_comm_groupPoint
#print axioms LeanCrypto.Proofs.BN254Group.add_assoc_groupPoint

#print axioms LeanCrypto.Proofs.BN254Group.groupPoint_zero_iff
