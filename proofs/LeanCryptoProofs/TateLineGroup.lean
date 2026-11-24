import LeanCryptoProofs.G2AffineLaw
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing
open BN254Fp2 BN254G2Group

theorem affine_ext {left right : Affine} (x : model left.x = model right.x)
    (y : model left.y = model right.y) : left = right := by
  have sameX := model_injective x
  have sameY := model_injective y
  cases left
  cases right
  cases sameX
  cases sameY
  rfl

theorem doubling_not_vertical (point : Affine) (nonzeroY : model point.y ≠ 0) :
    ¬(model point.x = model point.x ∧
      model point.y = curve.toAffine.negY (model point.x) (model point.y)) := by
  intro equal
  have negation := equal.2
  simp only [curve, WeierstrassCurve.Affine.negY, zero_mul, sub_zero] at negation
  have twice : (2 : BN254Fp2.Field) * model point.y = 0 := by linear_combination negation
  exact mul_ne_zero (by decide +kernel) nonzeroY twice

/-- For every pair of independently on-twist inputs and every independently
on-curve finite G1 evaluation point, the actual private line program constructs
a result representing addition in the established G2 elliptic-curve group. -/
theorem twist_line_construct (r s : Affine) (rCurve : r.onCurve = true) (sCurve : s.onCurve = true)
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true) :
    ∃ (factor : Fp12) (sum : Option Affine),
      nativeLineAndSum (embedG2 r) (embedG2 s) (embedG1 evaluation) =
        .ok (factor, sum.map embedG2) ∧
      Represents sum (affinePoint r rCurve + affinePoint s sCurve) := by
  by_cases sameX : model r.x = model s.x
  · by_cases negativeY : model r.y = -model s.y
    · have xShape : BN254Fp12.model (embedG2 r).x = BN254Fp12.model (embedG2 s).x := by
        rw [model_embedG2_x, model_embedG2_x, sameX]
      have yShape : BN254Fp12.model (embedG2 r).y = -BN254Fp12.model (embedG2 s).y := by
        rw [model_embedG2_y, model_embedG2_y]
        apply QuadraticAlgebra.ext <;> simp [negativeY]
      have constructed := line_vertical_construct (embedG2 r) (embedG2 s) (embedG1 evaluation)
        xShape yShape (twist_vertical_nonzero evaluation evaluationCurve r)
      refine ⟨_, none, constructed, ?_⟩
      change affinePoint r rCurve + affinePoint s sCurve = 0
      unfold affinePoint
      apply WeierstrassCurve.Affine.Point.add_of_Y_eq sameX
      simpa [curve, WeierstrassCurve.Affine.negY] using negativeY
    · have squares : model r.y ^ 2 = model s.y ^ 2 := by
        rw [(affine_onCurve_iff r).1 rCurve, (affine_onCurve_iff s).1 sCurve, sameX]
      have factored : (model r.y - model s.y) * (model r.y + model s.y) = 0 := by
        calc
          _ = model r.y ^ 2 - model s.y ^ 2 := by ring
          _ = 0 := by rw [squares]; ring
      have sameY : model r.y = model s.y := by
        rcases mul_eq_zero.mp factored with first | second
        · exact sub_eq_zero.mp first
        · exact False.elim (negativeY (eq_neg_of_add_eq_zero_left second))
      have same := affine_ext sameX sameY
      subst s
      have nonzeroY : model r.y ≠ 0 := by
        intro zero
        apply negativeY
        simp [zero]
      let slope := 3 * model r.x ^ 2 / (2 * model r.y)
      have notVertical := doubling_not_vertical r nonzeroY
      have admitted := g2Sum_admitted r r rCurve rCurve notVertical
      have represented := g2Sum_represents r r rCurve rCurve notVertical
      simp only [doubling_slope r nonzeroY] at admitted represented
      obtain ⟨factor, constructed⟩ := twist_double_construct r evaluation evaluationCurve nonzeroY
      exact ⟨factor, some (g2SumFromSlope r r slope), constructed, admitted, represented.symm⟩
  · have notVertical : ¬(model r.x = model s.x ∧
        model r.y = curve.toAffine.negY (model s.x) (model s.y)) := fun equal => sameX equal.1
    have admitted := g2Sum_admitted r s rCurve sCurve notVertical
    have represented := g2Sum_represents r s rCurve sCurve notVertical
    simp only [addition_slope r s sameX] at admitted represented
    obtain ⟨factor, constructed⟩ := twist_add_construct r s evaluation evaluationCurve sameX
    exact ⟨factor, some (g2SumFromSlope r s ((model s.y - model r.y) / (model s.x - model r.x))),
      constructed, admitted, represented.symm⟩

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.affine_ext
#print axioms LeanCrypto.Proofs.BN254Tate.doubling_not_vertical
#print axioms LeanCrypto.Proofs.BN254Tate.twist_line_construct
