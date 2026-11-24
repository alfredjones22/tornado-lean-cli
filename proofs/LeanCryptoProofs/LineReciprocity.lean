import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace LeanCrypto.Proofs.LineReciprocity

variable {R : Type*} [CommRing R]

/-- Symmetric cubic sectionData data, allowing repeated roots. Thus the
algebraic identity includes tangent, coincident and zero-factor cases. -/
structure Section (slope intercept coefficient : R) where
  x0 : R
  x1 : R
  x2 : R
  sum : x0 + x1 + x2 = slope ^ 2
  pairs : x0 * x1 + x0 * x2 + x1 * x2 = -2 * slope * intercept
  product : x0 * x1 * x2 = intercept ^ 2 - coefficient

def productFormula (slope intercept otherSlope otherIntercept coefficient : R) : R :=
  let a := slope - otherSlope
  let b := intercept - otherIntercept
  a ^ 3 * (intercept ^ 2 - coefficient) - 2 * a ^ 2 * b * slope * intercept +
    a * b ^ 2 * slope ^ 2 + b ^ 3

def evaluateOtherLine (slope intercept otherSlope otherIntercept coefficient : R)
    (sectionData : Section slope intercept coefficient) : R :=
  ((slope - otherSlope) * sectionData.x0 + (intercept - otherIntercept)) *
  ((slope - otherSlope) * sectionData.x1 + (intercept - otherIntercept)) *
  ((slope - otherSlope) * sectionData.x2 + (intercept - otherIntercept))

theorem three_linear_factors (a b x0 x1 x2 : R) :
    (a * x0 + b) * (a * x1 + b) * (a * x2 + b) =
      a ^ 3 * (x0 * x1 * x2) + a ^ 2 * b * (x0 * x1 + x0 * x2 + x1 * x2) +
        a * b ^ 2 * (x0 + x1 + x2) + b ^ 3 := by ring

theorem section_product (slope intercept otherSlope otherIntercept coefficient : R)
    (sectionData : Section slope intercept coefficient) :
    evaluateOtherLine slope intercept otherSlope otherIntercept coefficient sectionData =
      productFormula slope intercept otherSlope otherIntercept coefficient := by
  unfold evaluateOtherLine productFormula
  rw [three_linear_factors, sectionData.product, sectionData.pairs, sectionData.sum]
  ring

/-- The two degree-three line intersection products differ by sign.
This is a direct polynomial identity; no general reciprocity theorem,
nonzero denominator, distinctness or successful native pairing is assumed. -/
theorem product_formula_reciprocity (slope intercept otherSlope otherIntercept coefficient : R) :
    productFormula slope intercept otherSlope otherIntercept coefficient +
      productFormula otherSlope otherIntercept slope intercept coefficient = 0 := by
  unfold productFormula
  ring

theorem section_reciprocity (slope intercept otherSlope otherIntercept coefficient : R)
    (first : Section slope intercept coefficient) (second : Section otherSlope otherIntercept coefficient) :
    evaluateOtherLine slope intercept otherSlope otherIntercept coefficient first =
      -evaluateOtherLine otherSlope otherIntercept slope intercept coefficient second := by
  rw [section_product, section_product]
  exact eq_neg_of_add_eq_zero_left (product_formula_reciprocity slope intercept otherSlope otherIntercept coefficient)

end LeanCrypto.Proofs.LineReciprocity

#print axioms LeanCrypto.Proofs.LineReciprocity.three_linear_factors
#print axioms LeanCrypto.Proofs.LineReciprocity.section_product
#print axioms LeanCrypto.Proofs.LineReciprocity.product_formula_reciprocity
#print axioms LeanCrypto.Proofs.LineReciprocity.section_reciprocity
