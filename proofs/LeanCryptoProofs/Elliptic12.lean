import LeanCryptoProofs.TateEmbedding
import LeanCryptoProofs.G1GroupLaw

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.TatePairing

def curve12 : WeierstrassCurve BN254Fp12.Field := BN254Group.curve.map fpHom

instance curve12Elliptic : curve12.IsElliptic := by
  change (BN254Group.curve.map fpHom).IsElliptic
  infer_instance

theorem curve12_coefficients : curve12 = ⟨0, 0, 0, 0, 3⟩ := by
  unfold curve12 BN254Group.curve WeierstrassCurve.map
  simp only [map_zero, map_ofNat]

def modelPoint (point : Point) (onCurve : point.onCurve = true) : curve12.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some (BN254Fp12.model point.x) (BN254Fp12.model point.y)
    (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff, curve12_coefficients]
      simpa using (native_onCurve_iff point).1 onCurve))

abbrev FunctionField := curve12.toAffine.FunctionField
abbrev CoordinateRing := curve12.toAffine.CoordinateRing

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.curve12_coefficients
