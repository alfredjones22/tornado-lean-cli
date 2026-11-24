import LeanCryptoProofs.ScalarMulGroupLaw
import LeanCryptoProofs.NormalizationGroupLaw

namespace LeanCrypto.Proofs.BN254Group

open LeanCrypto.BN254.G1 LeanCrypto.Proofs.BN254Jacobian

theorem scalarMul_infinity (scalar : Nat) :
    Jacobian.infinity.scalarMul scalar = Jacobian.infinity := by
  apply (groupPoint_zero_iff _ (scalarMul_admissible _ scalar infinity_admissible)).mp
  rw [scalarMul_groupPoint _ scalar infinity_admissible, infinity_groupPoint]
  exact nsmul_zero _

/-- Actual normalization constructs the mathematical modular scalar multiple.
Neither native scalar multiplication nor normalization success is a premise. -/
theorem toAffine_scalarMul_represents_modular_multiple (point : Jacobian) (scalar : Nat)
    (admitted : Admissible point) :
    ∃ output, (point.scalarMul scalar).toAffine = .ok output ∧
      Represents output ((scalar % scalarPrime) • groupPoint point) := by
  obtain ⟨output, constructed, represented⟩ := toAffine_represents_groupPoint (point.scalarMul scalar)
    (scalarMul_admissible point scalar admitted)
  exact ⟨output, constructed, (scalarMul_groupPoint point scalar admitted) ▸ represented⟩

/-- Canonical callers below q obtain the ordinary natural scalar multiple,
without requiring or postulating that q is the group order. -/
theorem toAffine_scalarMul_represents_canonical_multiple (point : Jacobian) (scalar : Nat)
    (admitted : Admissible point) (canonical : scalar < scalarPrime) :
    ∃ output, (point.scalarMul scalar).toAffine = .ok output ∧
      Represents output (scalar • groupPoint point) := by
  obtain ⟨output, constructed, represented⟩ :=
    toAffine_scalarMul_represents_modular_multiple point scalar admitted
  exact ⟨output, constructed, by simpa only [Nat.mod_eq_of_lt canonical] using represented⟩

end LeanCrypto.Proofs.BN254Group

#print axioms LeanCrypto.Proofs.BN254Group.scalarMul_infinity
#print axioms LeanCrypto.Proofs.BN254Group.toAffine_scalarMul_represents_modular_multiple
#print axioms LeanCrypto.Proofs.BN254Group.toAffine_scalarMul_represents_canonical_multiple
