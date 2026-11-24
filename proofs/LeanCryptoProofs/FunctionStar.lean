import LeanCryptoProofs.CurveFunctionEvaluation
import LeanCryptoProofs.SubfieldReduction
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open Polynomial

def coordinateX : CoordinateRing := AdjoinRoot.of curve12.toAffine.polynomial X
def coordinateY : CoordinateRing := AdjoinRoot.root curve12.toAffine.polynomial

theorem curve_polynomial : curve12.toAffine.polynomial =
    (X ^ 2 - C (X ^ 3 + C (3 : BN254Fp12.Field))) := by
  rw [curve12_coefficients]
  simp [WeierstrassCurve.Affine.polynomial]

theorem coordinate_equation : coordinateY ^ 2 = coordinateX ^ 3 + 3 := by
  have rewriteEvaluation := congrArg
    (fun polynomial : Polynomial (Polynomial BN254Fp12.Field) =>
      eval₂ (AdjoinRoot.of curve12.toAffine.polynomial) coordinateY polynomial) curve_polynomial
  have equation : eval₂ (AdjoinRoot.of curve12.toAffine.polynomial) coordinateY
      (X ^ 2 - C (X ^ 3 + C (3 : BN254Fp12.Field))) = 0 :=
    rewriteEvaluation.symm.trans (AdjoinRoot.eval₂_root curve12.toAffine.polynomial)
  apply sub_eq_zero.mp
  simpa [coordinateX, coordinateY, eval₂_pow, eval₂_C, map_ofNat] using equation

def coefficientStar : BN254Fp12.Field →+* CoordinateRing :=
  (algebraMap BN254Fp12.Field CoordinateRing).comp (starRingEnd BN254Fp12.Field)

def polynomialStar : Polynomial BN254Fp12.Field →+* CoordinateRing :=
  Polynomial.eval₂RingHom coefficientStar coordinateX

def coordinateStar : CoordinateRing →+* CoordinateRing :=
  AdjoinRoot.lift polynomialStar (-coordinateY) (by
    calc
      eval₂ polynomialStar (-coordinateY) curve12.toAffine.polynomial =
          eval₂ polynomialStar (-coordinateY) (X ^ 2 - C (X ^ 3 + C (3 : BN254Fp12.Field))) :=
        congrArg (fun polynomial : Polynomial (Polynomial BN254Fp12.Field) =>
          eval₂ polynomialStar (-coordinateY) polynomial) curve_polynomial
      _ = 0 := by simp [polynomialStar, coefficientStar, coordinate_equation, eval₂_pow, eval₂_C, map_ofNat])

theorem coordinateStar_of (value : Polynomial BN254Fp12.Field) :
    coordinateStar (AdjoinRoot.of curve12.toAffine.polynomial value) = polynomialStar value := by
  exact AdjoinRoot.lift_of _

theorem coordinateStar_constant (value : BN254Fp12.Field) :
    coordinateStar (algebraMap BN254Fp12.Field CoordinateRing value) =
      algebraMap BN254Fp12.Field CoordinateRing (star value) := by
  change coordinateStar (AdjoinRoot.of curve12.toAffine.polynomial (C value)) = _
  rw [coordinateStar_of]
  simp [polynomialStar, coefficientStar]
  rfl

theorem coordinateStar_X : coordinateStar coordinateX = coordinateX := by
  rw [coordinateX, coordinateStar_of]
  simp [polynomialStar]
  rfl

theorem coordinateStar_Y : coordinateStar coordinateY = -coordinateY := by
  exact AdjoinRoot.lift_root _

theorem coordinateStar_twice_hom : coordinateStar.comp coordinateStar = RingHom.id CoordinateRing := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro value
      change coordinateStar (coordinateStar (algebraMap BN254Fp12.Field CoordinateRing value)) =
        algebraMap BN254Fp12.Field CoordinateRing value
      rw [coordinateStar_constant, coordinateStar_constant, star_star]
    · change coordinateStar (coordinateStar coordinateX) = coordinateX
      rw [coordinateStar_X, coordinateStar_X]
  · change coordinateStar (coordinateStar coordinateY) = coordinateY
    rw [coordinateStar_Y, map_neg, coordinateStar_Y, neg_neg]

theorem coordinateStar_involutive : Function.Involutive coordinateStar := by
  intro value
  exact congrArg (fun hom : CoordinateRing →+* CoordinateRing => hom value) coordinateStar_twice_hom

def coordinateStarEquiv : CoordinateRing ≃+* CoordinateRing where
  toFun := coordinateStar
  invFun := coordinateStar
  left_inv := coordinateStar_involutive
  right_inv := coordinateStar_involutive
  map_add' := coordinateStar.map_add
  map_mul' := coordinateStar.map_mul

def functionStar : FunctionField ≃+* FunctionField :=
  IsFractionRing.ringEquivOfRingEquiv coordinateStarEquiv

theorem functionStar_algebraMap (value : CoordinateRing) :
    functionStar (algebraMap CoordinateRing FunctionField value) =
      algebraMap CoordinateRing FunctionField (coordinateStar value) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap coordinateStarEquiv value

theorem functionStar_constant (value : BN254Fp12.Field) :
    functionStar (algebraMap CoordinateRing FunctionField (algebraMap BN254Fp12.Field CoordinateRing value)) =
      algebraMap CoordinateRing FunctionField (algebraMap BN254Fp12.Field CoordinateRing (star value)) := by
  rw [functionStar_algebraMap, coordinateStar_constant]

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.curve_polynomial
#print axioms LeanCrypto.Proofs.BN254Tate.coordinate_equation
#print axioms LeanCrypto.Proofs.BN254Tate.coordinateStar_of
#print axioms LeanCrypto.Proofs.BN254Tate.coordinateStar_constant
#print axioms LeanCrypto.Proofs.BN254Tate.coordinateStar_X
#print axioms LeanCrypto.Proofs.BN254Tate.coordinateStar_Y
#print axioms LeanCrypto.Proofs.BN254Tate.coordinateStar_twice_hom
#print axioms LeanCrypto.Proofs.BN254Tate.coordinateStar_involutive
#print axioms LeanCrypto.Proofs.BN254Tate.functionStar_algebraMap
#print axioms LeanCrypto.Proofs.BN254Tate.functionStar_constant
