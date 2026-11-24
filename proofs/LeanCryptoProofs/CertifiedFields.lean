import LeanCryptoProofs.Primes
import LeanCryptoProofs.FpModel
import LeanCryptoProofs.FrModel
import LeanCryptoProofs.JacobianModel

/-! Close the numerical primality hypotheses using kernel-checked certificates.
These are native representation/arithmetic and curve-preservation statements,
not group, pairing, Groth16 completeness or zero-knowledge theorems. -/

namespace LeanCrypto.Proofs.BN254Fp

instance certifiedModulusPrime : Fact P.Prime := ⟨Primes.bn254_base_prime⟩

theorem inverse_total_certified (value : LeanCrypto.BN254.G1.Fp) :
    value.inverse = if model value = 0 then .error "BN254 Fp zero has no inverse."
      else .ok (encode ((model value)⁻¹)) :=
  inverse_total value

end LeanCrypto.Proofs.BN254Fp

namespace LeanCrypto.Proofs.BN254Fr

instance certifiedModulusPrime : Fact Q.Prime := ⟨Primes.bn254_scalar_prime⟩

theorem inverse_total_certified (value : Nat) :
    LeanCrypto.Groth16.FFT.inverse value =
      if model value = 0 then .error "Fr zero has no inverse."
      else .ok ((model value)⁻¹).val :=
  inverse_total value

end LeanCrypto.Proofs.BN254Fr

namespace LeanCrypto.Proofs.BN254Jacobian

theorem double_preserves_curve_certified (point : LeanCrypto.BN254.G1.Jacobian)
    (admitted : Admissible point) : Admissible point.double :=
  double_admissible point admitted

theorem add_preserves_curve_certified (left right : LeanCrypto.BN254.G1.Jacobian)
    (leftAdmitted : Admissible left) (rightAdmitted : Admissible right) :
    Admissible (left.add right) :=
  add_admissible left right leftAdmitted rightAdmitted

end LeanCrypto.Proofs.BN254Jacobian

#print axioms LeanCrypto.Proofs.BN254Fp.inverse_total_certified
#print axioms LeanCrypto.Proofs.BN254Fr.inverse_total_certified
#print axioms LeanCrypto.Proofs.BN254Jacobian.double_preserves_curve_certified
#print axioms LeanCrypto.Proofs.BN254Jacobian.add_preserves_curve_certified
