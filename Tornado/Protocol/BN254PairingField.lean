import LeanCrypto.BN254.PairingField
import Tornado.Protocol.BN254G2

/-! Definitional compatibility aliases for the standalone implementation. -/

namespace Tornado.Protocol.BN254PairingField

export LeanCrypto.BN254.PairingField (nonresidue Fp6.zero Fp6.one Fp6.v Fp6.add Fp6.neg Fp6.sub Fp6.mulByV Fp6.mul Fp6.inverse Fp12.zero Fp12.one Fp12.w Fp12.add Fp12.neg Fp12.sub Fp12.conjugate Fp12.mul Fp12.square Fp12.pow Fp12.inverse fp6_inverse_sound fp12_inverse_sound Fp6 Fp6.mk Fp6.c0 Fp6.c1 Fp6.c2 Fp12 Fp12.mk Fp12.c0 Fp12.c1)

end Tornado.Protocol.BN254PairingField
