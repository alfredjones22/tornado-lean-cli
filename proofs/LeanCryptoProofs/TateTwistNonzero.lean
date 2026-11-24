import LeanCryptoProofs.TateEmbedding
import LeanCryptoProofs.FpCoordinateNonzero
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G1 LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField
open LeanCrypto.BN254.TatePairing

def slopeValue (value : BN254Fp2.Field) : BN254Fp12.Field :=
  ⟨0, algebraMap BN254Fp2.Field BN254Fp6.Field value⟩

theorem twist_vertical_nonzero (evaluation : LeanCrypto.BN254.G1.Affine)
    (onCurve : evaluation.onCurve = true) (point : LeanCrypto.BN254.G2.Affine) :
    BN254Fp12.model (embedG1 evaluation).x - BN254Fp12.model (embedG2 point).x ≠ 0 := by
  intro zero
  have nativeZero : (embedG1 evaluation).x.sub (embedG2 point).x = Fp12.zero :=
    BN254Fp12.model_injective (by rw [BN254Fp12.model_sub]; exact zero.trans BN254Fp12.model_zero.symm)
  have constantCoefficient := congrArg (fun value : Fp12 => BN254Fp.model value.c0.c0.c0) nativeZero
  simp [embedG1, embedFp, embedG2, Fp12.sub, Fp12.add, Fp12.neg, Fp12.zero,
    Fp6.add, Fp6.neg, Fp6.zero, Fp2.add, Fp2.neg, Fp2.zero] at constantCoefficient
  exact BN254G1Coordinates.affine_x_nonzero evaluation onCurve constantCoefficient

/-- A line through twist points has only odd-w terms apart from the
evaluation point's y-coordinate. The independent quadratic basis prevents
it from vanishing at any native finite on-curve G1 evaluation point. -/
theorem twist_line_nonzero (evaluation : LeanCrypto.BN254.G1.Affine)
    (onCurve : evaluation.onCurve = true) (point : LeanCrypto.BN254.G2.Affine)
    (slope : BN254Fp2.Field) :
    (BN254Fp12.model (embedG1 evaluation).y - BN254Fp12.model (embedG2 point).y) -
      slopeValue slope *
        (BN254Fp12.model (embedG1 evaluation).x - BN254Fp12.model (embedG2 point).x) ≠ 0 := by
  intro zero
  have realPart := congrArg QuadraticAlgebra.re zero
  simp only [embedG1, model_embedFp, model_embedG2_x, model_embedG2_y, fpHom, fp2Hom,
    RingHom.comp_apply, slopeValue, QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_sub,
    QuadraticAlgebra.re_zero, zero_mul, sub_zero] at realPart
  apply BN254G1Coordinates.affine_y_nonzero evaluation onCurve
  exact fpHom.injective (by simpa [fpHom, fp2Hom] using realPart)

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.twist_vertical_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.twist_line_nonzero
