import LeanCrypto.Constants
import Std

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254MillerPrefixes

abbrev q : Nat := LeanCrypto.bn254ScalarPrime
def bits : Nat := q.log2 + 1
def before (step : Nat) : Nat := q / 2 ^ (bits - step)
def after (step : Nat) : Nat := q / 2 ^ (bits - step - 1)
def digit (step : Nat) : Nat := q / 2 ^ (bits - step - 1) % 2
def steps : List Nat := List.range' 1 (bits - 1)

def validStep (step : Nat) : Bool := decide (
  0 < before step ∧ 2 * before step < q ∧
  after step = 2 * before step + digit step ∧
  0 < after step ∧ after step ≤ q ∧
  after step = before (step + 1) ∧
  (after step = q ↔ step = bits - 1))

set_option maxRecDepth 8192
set_option maxHeartbeats 0 in
theorem valid_steps_certificate : steps.all validStep = true := by decide +kernel

theorem valid_step (step : Nat) (member : step ∈ steps) :
    0 < before step ∧ 2 * before step < q ∧
    after step = 2 * before step + digit step ∧
    0 < after step ∧ after step ≤ q ∧
    after step = before (step + 1) ∧
    (after step = q ↔ step = bits - 1) := by
  exact of_decide_eq_true (List.all_eq_true.mp valid_steps_certificate step member)

theorem initial_prefix : before 1 = 1 := by decide +kernel
theorem final_prefix : after (bits - 1) = q := by decide +kernel

end LeanCrypto.Proofs.BN254MillerPrefixes
#print axioms LeanCrypto.Proofs.BN254MillerPrefixes.valid_steps_certificate
#print axioms LeanCrypto.Proofs.BN254MillerPrefixes.valid_step
#print axioms LeanCrypto.Proofs.BN254MillerPrefixes.initial_prefix
#print axioms LeanCrypto.Proofs.BN254MillerPrefixes.final_prefix
