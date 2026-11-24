import LeanCrypto.BN254.G2
import Tornado.Protocol.BN254G1

/-! Definitional compatibility aliases for the standalone implementation. -/

namespace Tornado.Protocol.BN254G2

export LeanCrypto.BN254.G2 (Fp2.zero Fp2.one Fp2.ofNats Fp2.add Fp2.neg Fp2.sub Fp2.mul Fp2.inverse twistB Affine.onCurve Affine.checked Jacobian.infinity Jacobian.ofAffine Jacobian.isInfinity Jacobian.double Jacobian.add Jacobian.scalarMul Jacobian.toAffine generator Fp2 Fp2.mk Fp2.c0 Fp2.c1 Affine Affine.mk Affine.x Affine.y Jacobian Jacobian.mk Jacobian.x Jacobian.y Jacobian.z)

end Tornado.Protocol.BN254G2
