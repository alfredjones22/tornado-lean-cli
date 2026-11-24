import LeanCryptoProofs.CurveFunctionEvaluation
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate

/-- Candidate normalized line function in the independent curve function field;
its principal-ideal relation is developed separately. -/
def normalizedLine : curve12.toAffine.Point → curve12.toAffine.Point → FunctionField
  | .zero, _ => 1
  | _, .zero => 1
  | .some x1 y1 _, .some x2 y2 _ =>
    if x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2 then verticalFunction x1
    else
      let slope := curve12.toAffine.slope x1 x2 y1 y2
      lineQuotient x1 y1 slope (curve12.toAffine.addX x1 x2 slope)

theorem normalizedLine_nonzero (first second : curve12.toAffine.Point) :
    normalizedLine first second ≠ 0 := by
  cases first with
  | zero => exact one_ne_zero
  | some x1 y1 h1 =>
    cases second with
    | zero => exact one_ne_zero
    | some x2 y2 h2 =>
      change (if x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2 then verticalFunction x1
        else lineQuotient x1 y1 (curve12.toAffine.slope x1 x2 y1 y2)
          (curve12.toAffine.addX x1 x2 (curve12.toAffine.slope x1 x2 y1 y2))) ≠ 0
      split
      · exact verticalFunction_nonzero _
      · exact div_ne_zero (lineFunction_nonzero _ _ _) (verticalFunction_nonzero _)

theorem normalizedLine_zero_left (point : curve12.toAffine.Point) : normalizedLine 0 point = 1 := rfl
theorem normalizedLine_zero_right (point : curve12.toAffine.Point) : normalizedLine point 0 = 1 := by
  cases point <;> rfl

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.normalizedLine_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.normalizedLine_zero_left
#print axioms LeanCrypto.Proofs.BN254Tate.normalizedLine_zero_right
