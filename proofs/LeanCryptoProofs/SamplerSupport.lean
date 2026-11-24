import LeanCryptoProofs.SamplerField

set_option autoImplicit false

namespace LeanCrypto.Proofs.SamplerField

open LeanCrypto.Probability.Rejection LeanCrypto.Sampling

theorem pairMass_congr_admissible (D q budget : Nat) (positive : 0 < q) (fits : q ≤ D)
    (first second : Option (Nat × Nat) → Nat) (failure : first none = second none)
    (success : ∀ r s, 0 < r → r < q → 0 < s → s < q →
      first (some (r, s)) = second (some (r, s))) :
    pairMass D q budget first = pairMass D q budget second := by
  rw [pair_event_formula D q budget positive fits first,
    pair_event_formula D q budget positive fits second, failure]
  congr 1
  apply congrArg (fun value => successWeight D q budget ^ 2 * value)
  apply sumTo_congr
  intro r rBound
  apply sumTo_congr
  intro s sBound
  apply success (r + 1) (s + 1) <;> omega

end LeanCrypto.Proofs.SamplerField

#print axioms LeanCrypto.Proofs.SamplerField.pairMass_congr_admissible
