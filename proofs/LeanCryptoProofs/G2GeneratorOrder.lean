import LeanCrypto.BN254.G2

/-! Closed numerical certificate over the actual total, nonreducing native
G2 scalar loop. This is not the vacuous multiplication of a reduced scalar. -/
set_option autoImplicit false
set_option maxRecDepth 8192

namespace LeanCrypto.Proofs.BN254G2Order
open LeanCrypto.BN254.G2

set_option maxHeartbeats 0 in
theorem generator_raw_q_order :
    ((Jacobian.ofAffine generator).scalarMulLoop LeanCrypto.BN254.G1.scalarPrime
      Jacobian.infinity).isInfinity = true := by
  decide +kernel

theorem generator_public_q_order :
    ((Jacobian.ofAffine generator).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true :=
  generator_raw_q_order

end LeanCrypto.Proofs.BN254G2Order

#print axioms LeanCrypto.Proofs.BN254G2Order.generator_raw_q_order
#print axioms LeanCrypto.Proofs.BN254G2Order.generator_public_q_order
