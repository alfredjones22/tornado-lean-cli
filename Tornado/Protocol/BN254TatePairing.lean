import LeanCrypto.BN254.TatePairing
import Tornado.Protocol.BN254PairingField

/-! Definitional compatibility aliases for the standalone implementation. -/

namespace Tornado.Protocol.BN254TatePairing

export LeanCrypto.BN254.TatePairing (finalExponent_divisible embedFp embedFp2 Point.onCurve embedG2 embedG1 miller pair pair_success_nonzero pair_success_order Point Point.mk Point.x Point.y)

end Tornado.Protocol.BN254TatePairing
