import LeanCrypto.Groth16.Verify
import Tornado.Protocol.BN254TatePairing

/-! Definitional compatibility aliases for the standalone implementation. -/

namespace Tornado.Protocol.BN254Groth16Verify

export LeanCrypto.Groth16.Verify (publicInputPoint publicInputPoint_success_signals_bounded verify verify_true_signals_bounded VerifyingKey VerifyingKey.mk VerifyingKey.alpha1 VerifyingKey.beta2 VerifyingKey.gamma2 VerifyingKey.delta2 VerifyingKey.ic Proof Proof.mk Proof.a Proof.b Proof.c)

end Tornado.Protocol.BN254Groth16Verify
