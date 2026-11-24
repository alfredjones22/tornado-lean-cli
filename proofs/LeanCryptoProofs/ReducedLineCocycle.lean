import LeanCryptoProofs.TwistEvaluation
import LeanCryptoProofs.ReducedFunctionEvaluation
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

def evaluatedLine (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup) : BN254Fp12.Field :=
  Classical.choose (normalizedLine_evaluates evaluation onCurve first.val second.val first.property second.property)

theorem evaluatedLine_nonzero (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup) : evaluatedLine evaluation onCurve first second ≠ 0 :=
  (Classical.choose_spec (normalizedLine_evaluates evaluation onCurve first.val second.val first.property second.property)).1

theorem evaluatedLine_evaluates (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup) :
    Evaluates (embedG1 evaluation) (embedG1_onCurve evaluation onCurve)
      (normalizedLine first.val second.val) (evaluatedLine evaluation onCurve first second) :=
  (Classical.choose_spec (normalizedLine_evaluates evaluation onCurve first.val second.val first.property second.property)).2

def reducedLine (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup) : BN254Fp12.Field :=
  evaluatedLine evaluation onCurve first second ^ finalExponent

theorem evaluatedLine_zero_left (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (point : twistSubgroup) : evaluatedLine evaluation onCurve 0 point = 1 := by
  have evaluated := evaluatedLine_evaluates evaluation onCurve 0 point
  change Evaluates (embedG1 evaluation) (embedG1_onCurve evaluation onCurve)
    (normalizedLine 0 point.val) _ at evaluated
  rw [normalizedLine_zero_left] at evaluated
  exact evaluates_unique _ _ 1 _ 1 evaluated (evaluates_one _ _)

theorem reducedLine_zero_left (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (point : twistSubgroup) : reducedLine evaluation onCurve 0 point = 1 := by
  rw [reducedLine, evaluatedLine_zero_left, one_pow]

theorem reducedLine_symmetric (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup) :
    reducedLine evaluation onCurve first second = reducedLine evaluation onCurve second first := by
  have same : principal (normalizedLine first.val second.val) (normalizedLine_nonzero _ _) =
      principal (normalizedLine second.val first.val) (normalizedLine_nonzero _ _) := by
    rw [principal_line_formula, principal_line_formula, add_comm first.val second.val,
      mul_comm (pointIdeal first.val) (pointIdeal second.val)]
  have secondStar : functionStar (normalizedLine second.val first.val) =
      (lineSign first.val second.val : FunctionField) * normalizedLine second.val first.val := by
    rw [normalizedLine_star _ _ second.property first.property, lineSign_symmetric second.val first.val]
  exact (principal_common_star_reduced (embedG1 evaluation) (embedG1_onCurve evaluation onCurve)
    _ _ (lineSign first.val second.val : FunctionField) (normalizedLine_nonzero _ _) (normalizedLine_nonzero _ _)
    (lineSign first.val second.val).ne_zero same
    (normalizedLine_star _ _ first.property second.property) secondStar
    _ _ (evaluatedLine_evaluates evaluation onCurve first second)
      (evaluatedLine_evaluates evaluation onCurve second first)).symm

theorem reducedLine_cocycle (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second third : twistSubgroup) :
    reducedLine evaluation onCurve first second * reducedLine evaluation onCurve (first + second) third =
      reducedLine evaluation onCurve first (second + third) * reducedLine evaluation onCurve second third := by
  let f := normalizedLine first.val second.val * normalizedLine (first.val + second.val) third.val
  let g := normalizedLine first.val (second.val + third.val) * normalizedLine second.val third.val
  let scale := (lineSign first.val second.val * lineSign (first.val + second.val) third.val : FunctionFieldˣ)
  have firstStar : functionStar f = (scale : FunctionField) * f := by
    dsimp only [f, scale]
    rw [map_mul, normalizedLine_star _ _ first.property second.property,
      normalizedLine_star _ _ (twistPoint_add _ _ first.property second.property) third.property, Units.val_mul]
    ring
  have secondStar : functionStar g = (scale : FunctionField) * g := by
    dsimp only [g, scale]
    rw [map_mul, normalizedLine_star _ _ first.property (twistPoint_add _ _ second.property third.property),
      normalizedLine_star _ _ second.property third.property]
    rw [lineSign_cocycle]
    simp only [Units.val_mul]
    ring
  have same : principal f (mul_ne_zero (normalizedLine_nonzero _ _) (normalizedLine_nonzero _ _)) =
      principal g (mul_ne_zero (normalizedLine_nonzero _ _) (normalizedLine_nonzero _ _)) := by
    rw [principal_product, principal_product]
    exact line_principal_cocycle first.val second.val third.val
  have firstEvaluated := evaluates_mul (embedG1 evaluation) (embedG1_onCurve evaluation onCurve) _ _ _ _
    (evaluatedLine_evaluates evaluation onCurve first second)
    (evaluatedLine_evaluates evaluation onCurve (first + second) third)
  have secondEvaluated := evaluates_mul (embedG1 evaluation) (embedG1_onCurve evaluation onCurve) _ _ _ _
    (evaluatedLine_evaluates evaluation onCurve first (second + third))
    (evaluatedLine_evaluates evaluation onCurve second third)
  have equality := principal_common_star_reduced (embedG1 evaluation) (embedG1_onCurve evaluation onCurve)
    f g (scale : FunctionField) (mul_ne_zero (normalizedLine_nonzero _ _) (normalizedLine_nonzero _ _))
    (mul_ne_zero (normalizedLine_nonzero _ _) (normalizedLine_nonzero _ _)) scale.ne_zero same
    firstStar secondStar _ _ firstEvaluated secondEvaluated
  simpa only [reducedLine, mul_pow] using equality.symm

theorem reducedLine_q_order (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup) : reducedLine evaluation onCurve first second ^ LeanCrypto.BN254.G1.scalarPrime = 1 := by
  rw [reducedLine, ← pow_mul, final_exponent_product]
  exact BN254Fp12.field_fermat _ (evaluatedLine_nonzero evaluation onCurve first second)

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.evaluatedLine_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.evaluatedLine_evaluates
#print axioms LeanCrypto.Proofs.BN254Tate.evaluatedLine_zero_left
#print axioms LeanCrypto.Proofs.BN254Tate.reducedLine_zero_left
#print axioms LeanCrypto.Proofs.BN254Tate.reducedLine_symmetric
#print axioms LeanCrypto.Proofs.BN254Tate.reducedLine_cocycle
#print axioms LeanCrypto.Proofs.BN254Tate.reducedLine_q_order
