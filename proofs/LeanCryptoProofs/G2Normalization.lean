import LeanCryptoProofs.G2JacobianModel
import Mathlib.Tactic.Ring

/-!
Constructive completeness of the actual G2 Jacobian normalization guards.
The admitted finite curve equation and the closed base-prime certificate
suffice. This does not establish an elliptic-curve group law or MSM semantics.
-/
set_option autoImplicit false

namespace LeanCrypto.Proofs.BN254G2Jacobian

open LeanCrypto.BN254.G2 LeanCrypto.Proofs.BN254Fp2

/-- Same inverse, square, cube and coordinate multiply chain as toAffine. -/
def normalizedAffine (point : Jacobian) : Affine :=
  let inverse := encode ((model point.z)⁻¹)
  let square := inverse.mul inverse
  let cube := square.mul inverse
  ⟨point.x.mul square, point.y.mul cube⟩

theorem normalized_x (point : Jacobian) :
    model (normalizedAffine point).x = model point.x * (model point.z)⁻¹ ^ 2 := by
  simp only [normalizedAffine, model_mul, model_encode]
  ring

theorem normalized_y (point : Jacobian) :
    model (normalizedAffine point).y = model point.y * (model point.z)⁻¹ ^ 3 := by
  simp only [normalizedAffine, model_mul, model_encode]
  ring

/-- Pure field identity, with no reference to normalization success. -/
theorem normalization_curve_identity {F : Type} [_root_.Field F] (coefficient x y z : F)
    (nonzero : z ≠ 0) (curve : y ^ 2 = x ^ 3 + coefficient * z ^ 6) :
    (y * z⁻¹ ^ 3) ^ 2 = (x * z⁻¹ ^ 2) ^ 3 + coefficient := by
  have cancel : z ^ 6 * z⁻¹ ^ 6 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ nonzero]
    norm_num
  calc
    _ = y ^ 2 * z⁻¹ ^ 6 := by ring
    _ = (x ^ 3 + coefficient * z ^ 6) * z⁻¹ ^ 6 := by rw [curve]
    _ = x ^ 3 * z⁻¹ ^ 6 + coefficient * (z ^ 6 * z⁻¹ ^ 6) := by ring
    _ = _ := by rw [cancel]; ring

theorem normalized_onCurve (point : Jacobian) (nonzero : model point.z ≠ 0)
    (curve : ProjectiveEquation point) : (normalizedAffine point).onCurve = true := by
  apply (affine_onCurve_iff _).2
  rw [normalized_x, normalized_y]
  exact normalization_curve_identity (model twistB) _ _ _ nonzero curve

theorem finite_not_infinity (point : Jacobian) (nonzero : model point.z ≠ 0) :
    point.isInfinity = false := by
  apply Bool.eq_false_iff.mpr
  intro infinite
  exact nonzero ((isInfinity_iff point).1 infinite)

/-- Both actual runtime guards are discharged from independent source
conditions. There is no successful toAffine call among the premises. -/
theorem toAffine_finite_construct (point : Jacobian) (nonzero : model point.z ≠ 0)
    (curve : ProjectiveEquation point) :
    point.toAffine = .ok (some (normalizedAffine point)) := by
  have finite := finite_not_infinity point nonzero
  have inverse := inverse_complete point.z nonzero
  have onCurve := normalized_onCurve point nonzero curve
  simp only [Jacobian.toAffine, finite, Bool.false_eq_true, ↓reduceIte,
    inverse, bind, Except.bind]
  change (if !(normalizedAffine point).onCurve then
    Except.error "BN254 G2 normalization produced an off-twist point."
    else Except.ok (some (normalizedAffine point))) = _
  rw [onCurve]
  rfl

theorem toAffine_infinity_construct : Jacobian.infinity.toAffine = .ok none := by
  simp only [Jacobian.toAffine, Jacobian.isInfinity, Jacobian.infinity]
  rfl

/-- Exact total result of the actual normalizer on every admitted input. -/
theorem toAffine_admissible_construct (point : Jacobian) (admitted : Admissible point) :
    point.toAffine = .ok (if point.isInfinity then none else some (normalizedAffine point)) := by
  rcases admitted with infinite | ⟨nonzero, curve⟩
  · subst point
    rw [toAffine_infinity_construct]
    rfl
  · rw [toAffine_finite_construct point nonzero curve, finite_not_infinity point nonzero]
    rfl

theorem toAffine_admissible_exists (point : Jacobian) (admitted : Admissible point) :
    ∃ result, point.toAffine = .ok result ∧
      (∀ affine, result = some affine → affine.onCurve = true) := by
  rcases admitted with infinite | ⟨nonzero, curve⟩
  · subst point
    exact ⟨none, toAffine_infinity_construct, by intro affine impossible; cases impossible⟩
  · exact ⟨some (normalizedAffine point), toAffine_finite_construct point nonzero curve,
      by intro affine same; cases same; exact normalized_onCurve point nonzero curve⟩

theorem toAffine_admissible_no_error (point : Jacobian) (admitted : Admissible point)
    (error : String) : point.toAffine ≠ .error error := by
  rw [toAffine_admissible_construct point admitted]
  intro impossible
  cases impossible

/-- The nonhomogeneous native infinity sentinel is handled explicitly. -/
theorem toAffine_admissible_none_iff (point : Jacobian) (admitted : Admissible point) :
    point.toAffine = .ok none ↔ point = Jacobian.infinity := by
  constructor
  · intro noneResult
    rcases admitted with infinite | ⟨nonzero, curve⟩
    · exact infinite
    · rw [toAffine_finite_construct point nonzero curve] at noneResult
      cases noneResult
  · intro infinite
    subst point
    exact toAffine_infinity_construct

theorem normalized_ofAffine (point : Affine) :
    normalizedAffine (Jacobian.ofAffine point) = point := by
  have x : (normalizedAffine (Jacobian.ofAffine point)).x = point.x := by
    apply model_injective
    simp [normalized_x, Jacobian.ofAffine]
  have y : (normalizedAffine (Jacobian.ofAffine point)).y = point.y := by
    apply model_injective
    simp [normalized_y, Jacobian.ofAffine]
  have extensionality : ∀ (a b : Affine), a.x = b.x → a.y = b.y → a = b := by
    intro a b sameX sameY
    cases a
    cases b
    cases sameX
    cases sameY
    rfl
  exact extensionality _ _ x y

/-- Construction for every independently on-curve affine input. -/
theorem toAffine_ofAffine_construct (point : Affine) (curve : point.onCurve = true) :
    (Jacobian.ofAffine point).toAffine = .ok (some point) := by
  have finite : model (Jacobian.ofAffine point).z ≠ 0 := by
    simp [Jacobian.ofAffine]
  have equation : ProjectiveEquation (Jacobian.ofAffine point) := by
    simpa [ProjectiveEquation, Jacobian.ofAffine] using (affine_onCurve_iff point).1 curve
  rw [toAffine_finite_construct _ finite equation, normalized_ofAffine]

end LeanCrypto.Proofs.BN254G2Jacobian

#print axioms LeanCrypto.Proofs.BN254G2Jacobian.normalized_x
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.normalized_y
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.normalization_curve_identity
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.normalized_onCurve
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.finite_not_infinity
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.toAffine_finite_construct
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.toAffine_infinity_construct
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.toAffine_admissible_construct
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.toAffine_admissible_exists
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.toAffine_admissible_no_error
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.toAffine_admissible_none_iff
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.normalized_ofAffine
#print axioms LeanCrypto.Proofs.BN254G2Jacobian.toAffine_ofAffine_construct
