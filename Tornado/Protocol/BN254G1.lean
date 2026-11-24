import LeanCrypto.BN254.G1
import Tornado.Protocol.Groth16R1CS

/-! Definitional compatibility aliases for the standalone implementation. -/

namespace Tornado.Protocol.BN254G1

export LeanCrypto.BN254.G1 (basePrime scalarPrime Fp.ofNat Fp.zero Fp.one Fp.add Fp.mul Fp.neg Fp.sub Fp.pow Fp.inverse fp_ofNat_bounded fp_add_bounded fp_mul_bounded fp_inverse_sound Affine.onCurve Affine.checked Jacobian.infinity Jacobian.ofAffine Jacobian.isInfinity Jacobian.double Jacobian.add Jacobian.scalarMul Jacobian.toAffine generator Fp Fp.mk Fp.val Fp.bounded Affine Affine.mk Affine.x Affine.y Jacobian Jacobian.mk Jacobian.x Jacobian.y Jacobian.z)

end Tornado.Protocol.BN254G1
