import LeanCryptoProofs.FunctionStar
import LeanCryptoProofs.LineCocyclePrincipal
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open Polynomial

theorem verticalClass_formula (x : BN254Fp12.Field) :
    verticalClass x = coordinateX - algebraMap BN254Fp12.Field CoordinateRing x := by
  change (AdjoinRoot.of curve12.toAffine.polynomial) (X - C x) = _
  rw [map_sub]
  rfl

theorem lineClass_formula (x y slope : BN254Fp12.Field) :
    lineClass x y slope = (coordinateY - algebraMap BN254Fp12.Field CoordinateRing y) -
      algebraMap BN254Fp12.Field CoordinateRing slope *
        (coordinateX - algebraMap BN254Fp12.Field CoordinateRing x) := by
  change (AdjoinRoot.mk curve12.toAffine.polynomial)
    (X - C (WeierstrassCurve.Affine.linePolynomial x y slope)) = _
  rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, WeierstrassCurve.Affine.linePolynomial, _root_.map_add, _root_.map_mul, _root_.map_sub]
  change coordinateY - ((algebraMap BN254Fp12.Field CoordinateRing slope) *
    (coordinateX - algebraMap BN254Fp12.Field CoordinateRing x) +
      algebraMap BN254Fp12.Field CoordinateRing y) = _
  ring

theorem coordinateStar_vertical (x : BN254Fp12.Field) (fixed : star x = x) :
    coordinateStar (verticalClass x) = verticalClass x := by
  simp only [verticalClass_formula, map_sub, coordinateStar_X, coordinateStar_constant, fixed]

theorem coordinateStar_line (x y slope : BN254Fp12.Field)
    (realX : star x = x) (imaginaryY : star y = -y) (imaginarySlope : star slope = -slope) :
    coordinateStar (lineClass x y slope) = -lineClass x y slope := by
  simp only [lineClass_formula, map_sub, map_mul, coordinateStar_X, coordinateStar_Y,
    coordinateStar_constant, realX, imaginaryY, imaginarySlope, map_neg]
  ring

theorem functionStar_vertical (x : BN254Fp12.Field) (fixed : star x = x) :
    functionStar (verticalFunction x) = verticalFunction x := by
  rw [verticalFunction, functionStar_algebraMap, coordinateStar_vertical x fixed]

theorem functionStar_line (x y slope : BN254Fp12.Field)
    (realX : star x = x) (imaginaryY : star y = -y) (imaginarySlope : star slope = -slope) :
    functionStar (lineFunction x y slope) = -lineFunction x y slope := by
  rw [lineFunction, functionStar_algebraMap, coordinateStar_line x y slope realX imaginaryY imaginarySlope, map_neg]

theorem functionStar_quotient (x y slope sumX : BN254Fp12.Field)
    (realX : star x = x) (imaginaryY : star y = -y) (imaginarySlope : star slope = -slope)
    (realSumX : star sumX = sumX) :
    functionStar (lineQuotient x y slope sumX) = -lineQuotient x y slope sumX := by
  rw [lineQuotient, map_div₀, functionStar_line x y slope realX imaginaryY imaginarySlope,
    functionStar_vertical sumX realSumX]
  exact _root_.neg_div _ _

theorem constantFunction_injective : Function.Injective constantFunction :=
  (IsFractionRing.injective CoordinateRing FunctionField).comp
    (algebraMap BN254Fp12.Field CoordinateRing).injective

theorem functionStar_constantFunction (value : BN254Fp12.Field) :
    functionStar (constantFunction value) = constantFunction (star value) := by
  exact functionStar_constant value

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.verticalClass_formula
#print axioms LeanCrypto.Proofs.BN254Tate.lineClass_formula
#print axioms LeanCrypto.Proofs.BN254Tate.coordinateStar_vertical
#print axioms LeanCrypto.Proofs.BN254Tate.coordinateStar_line
#print axioms LeanCrypto.Proofs.BN254Tate.functionStar_vertical
#print axioms LeanCrypto.Proofs.BN254Tate.functionStar_line
#print axioms LeanCrypto.Proofs.BN254Tate.functionStar_quotient
#print axioms LeanCrypto.Proofs.BN254Tate.constantFunction_injective
#print axioms LeanCrypto.Proofs.BN254Tate.functionStar_constantFunction
