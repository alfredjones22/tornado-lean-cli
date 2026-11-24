import LeanCryptoProofs.TwistGroup
import LeanCryptoProofs.LineReciprocity

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open Polynomial

def section_of_polynomial {R : Type} [CommRing R] (slope intercept coefficient x0 x1 x2 : R)
    (factorization : (C slope * X + C intercept) ^ 2 - (X ^ 3 + C coefficient) =
      -((X - C x0) * (X - C x1) * (X - C x2))) :
    LineReciprocity.Section slope intercept coefficient := by
  have cubics : (⟨-1, slope ^ 2, 2 * slope * intercept, intercept ^ 2 - coefficient⟩ : Cubic R) =
      ⟨-1, x0 + x1 + x2, -(x0 * x1 + x0 * x2 + x1 * x2), x0 * x1 * x2⟩ := by
    apply (Cubic.toPoly_injective _ _).mp
    calc
      _ = (C slope * X + C intercept) ^ 2 - (X ^ 3 + C coefficient) := by
        simp [Cubic.toPoly, map_sub, map_mul, map_pow, map_ofNat]
        ring
      _ = -((X - C x0) * (X - C x1) * (X - C x2)) := factorization
      _ = _ := by
        simp [Cubic.toPoly, map_add, map_mul]
        ring
  refine ⟨x0, x1, x2, ?_, ?_, ?_⟩
  · exact (congrArg Cubic.b cubics).symm
  · have equality := congrArg Cubic.c cubics
    change 2 * slope * intercept = -(x0 * x1 + x0 * x2 + x1 * x2) at equality
    linear_combination equality
  · exact (congrArg Cubic.d cubics).symm

def chordSlope (x1 x2 y1 y2 : BN254Fp12.Field) := curve12.toAffine.slope x1 x2 y1 y2
def chordIntercept (x1 x2 y1 y2 : BN254Fp12.Field) := y1 - chordSlope x1 x2 y1 y2 * x1

theorem chord_line_polynomial (x1 x2 y1 y2 : BN254Fp12.Field) :
    WeierstrassCurve.Affine.linePolynomial x1 y1 (chordSlope x1 x2 y1 y2) =
      C (chordSlope x1 x2 y1 y2) * X + C (chordIntercept x1 x2 y1 y2) := by
  unfold WeierstrassCurve.Affine.linePolynomial chordIntercept
  rw [map_sub, map_mul]
  ring

theorem chord_factorization (x1 x2 y1 y2 : BN254Fp12.Field)
    (first : curve12.toAffine.Equation x1 y1) (second : curve12.toAffine.Equation x2 y2)
    (notVertical : ¬(x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2)) :
    (C (chordSlope x1 x2 y1 y2) * X + C (chordIntercept x1 x2 y1 y2)) ^ 2 -
      (X ^ 3 + C (3 : BN254Fp12.Field)) =
        -((X - C x1) * (X - C x2) *
          (X - C (curve12.toAffine.addX x1 x2 (chordSlope x1 x2 y1 y2)))) := by
  have factorization := WeierstrassCurve.Affine.addPolynomial_slope first second notVertical
  change curve12.toAffine.addPolynomial x1 y1 (chordSlope x1 x2 y1 y2) = _ at factorization
  rw [WeierstrassCurve.Affine.addPolynomial, curve_polynomial, chord_line_polynomial] at factorization
  simpa only [eval_sub, eval_pow, eval_X, eval_C] using factorization

def chordSection (x1 x2 y1 y2 : BN254Fp12.Field)
    (first : curve12.toAffine.Equation x1 y1) (second : curve12.toAffine.Equation x2 y2)
    (notVertical : ¬(x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2)) :
    LineReciprocity.Section (chordSlope x1 x2 y1 y2) (chordIntercept x1 x2 y1 y2) (3 : BN254Fp12.Field) :=
  section_of_polynomial _ _ _ x1 x2 (curve12.toAffine.addX x1 x2 (chordSlope x1 x2 y1 y2))
    (chord_factorization x1 x2 y1 y2 first second notVertical)

theorem chord_reciprocity (x1 x2 y1 y2 z1 z2 v1 v2 : BN254Fp12.Field)
    (first : curve12.toAffine.Equation x1 y1) (second : curve12.toAffine.Equation x2 y2)
    (third : curve12.toAffine.Equation z1 v1) (fourth : curve12.toAffine.Equation z2 v2)
    (firstNotVertical : ¬(x1 = x2 ∧ y1 = curve12.toAffine.negY x2 y2))
    (secondNotVertical : ¬(z1 = z2 ∧ v1 = curve12.toAffine.negY z2 v2)) :
    LineReciprocity.evaluateOtherLine (chordSlope x1 x2 y1 y2) (chordIntercept x1 x2 y1 y2)
      (chordSlope z1 z2 v1 v2) (chordIntercept z1 z2 v1 v2) 3
      (chordSection x1 x2 y1 y2 first second firstNotVertical) =
    -LineReciprocity.evaluateOtherLine (chordSlope z1 z2 v1 v2) (chordIntercept z1 z2 v1 v2)
      (chordSlope x1 x2 y1 y2) (chordIntercept x1 x2 y1 y2) 3
      (chordSection z1 z2 v1 v2 third fourth secondNotVertical) :=
  LineReciprocity.section_reciprocity _ _ _ _ _ _ _

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.chord_line_polynomial
#print axioms LeanCrypto.Proofs.BN254Tate.chord_factorization
#print axioms LeanCrypto.Proofs.BN254Tate.chord_reciprocity
