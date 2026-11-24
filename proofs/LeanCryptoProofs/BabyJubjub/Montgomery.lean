import LeanCryptoProofs.BabyJubjub.Parameters
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BN254Fr
abbrev Field := ZMod Q

def curve : WeierstrassCurve.Affine Field := ⟨0,168698,0,1,0⟩

theorem curve_discriminant : curve.Δ = (16*(168698^2-4) : Field) := by
  decide +kernel

instance curve_elliptic : curve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by decide +kernel)⟩

abbrev Point := curve.Point

def Edwards (x y : Field) : Prop := 168700*x^2+y^2=1+168696*x^2*y^2

def Montgomery (u v : Field) : Prop := v^2=u^3+168698*u^2+u

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.curve_discriminant
