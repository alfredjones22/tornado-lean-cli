import LeanCryptoProofs.FFT.NativeTransform
open Lean Elab Term Meta
elab "actualNextPowerGo" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `Init.Data.Nat.Power2.Basic `Nat.nextPowerOfTwo.go)
elab "actualNextPowerGoEquation" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `Init.Data.Nat.Power2.Basic `Nat.nextPowerOfTwo.go.eq_def)

set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

abbrev nextPowerGo (number power : Nat) (positive : 0 < power) : Nat :=
  actualNextPowerGo number power positive

theorem nextPowerGo_equation (number power : Nat) (positive : 0 < power) :
    nextPowerGo number power positive =
      if power < number then nextPowerGo number (power * 2) (Nat.mul_pos positive (by decide))
      else power := by
  simpa only [dite_eq_ite] using (actualNextPowerGoEquation number power positive)


theorem nextPower_go_lower (number power : Nat) (positive : 0 < power) :
    number ≤ nextPowerGo number power positive := by
  rw [nextPowerGo_equation]
  split
  · exact nextPower_go_lower number (power * 2) (Nat.mul_pos positive (by decide))
  · omega
termination_by number - power
decreasing_by exact Nat.nextPowerOfTwo_dec positive (by assumption)

theorem nextPower_lower (number : Nat) : number ≤ number.nextPowerOfTwo :=
  nextPower_go_lower number 1 (by decide)

theorem nextPower_go_exact (bits power number : Nat) (positive : 0 < power)
    (initial : power = 2 ^ bits) (bound : number ≤ 2 ^ bits) :
    nextPowerGo number power positive = 2 ^ bits := by
  rw [nextPowerGo_equation, if_neg (by omega), initial]

theorem nextPower_go_target (total bits number : Nat)
    (stageBound : bits ≤ total) (lower : 2 ^ total / 2 < number) (upper : number ≤ 2 ^ total) :
    nextPowerGo number (2 ^ bits) (pow_pos (by decide) _) = 2 ^ total := by
  by_cases done : bits = total
  · subst bits
    exact nextPower_go_exact total _ _ _ rfl upper
  · have within : bits < total := by omega
    have small : 2 ^ bits ≤ 2 ^ total / 2 := by
      have totalPositive : 0 < total := by omega
      have successor : total - 1 + 1 = total := by omega
      rw [← successor, pow_succ, Nat.mul_div_cancel _ (by decide)]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [nextPowerGo_equation, if_pos (show 2 ^ bits < number by omega)]
    have next : 2 ^ bits * 2 = 2 ^ (bits + 1) := (pow_succ _ _).symm
    simp only [next]
    exact nextPower_go_target total (bits + 1) number (by omega) lower upper
termination_by total - bits

theorem nextPower_exact (total number : Nat)
    (lower : 2 ^ total / 2 < number) (upper : number ≤ 2 ^ total) :
    number.nextPowerOfTwo = 2 ^ total := by
  exact nextPower_go_target total 0 number (by omega) lower upper

def padded (input : Array Nat) (length : Nat) : Array Nat :=
  input ++ Array.replicate (length - input.size) 0

theorem padded_size (input : Array Nat) (length : Nat) (bounded : input.size ≤ length) :
    (padded input length).size = length := by
  simp only [padded, Array.size_append, Array.size_replicate]
  omega

theorem padded_lookup (input : Array Nat) (length index : Nat) :
    fieldInput (padded input length) index = fieldInput input index := by
  by_cases original : index < input.size
  · have inPadded : index < (padded input length).size := by
      simp only [padded, Array.size_append, Array.size_replicate]
      omega
    unfold fieldInput
    rw [getElem!_pos (padded input length) index inPadded, getElem!_pos input index original]
    simp only [padded, Array.getElem_append, original, ↓reduceDIte]
  · by_cases padding : index < (padded input length).size
    · unfold fieldInput
      rw [getElem!_pos (padded input length) index padding, getElem!_neg input index original]
      simp only [padded, Array.getElem_append, original, ↓reduceDIte, Array.getElem_replicate]
      rfl
    · simp [fieldInput, getElem!_neg (padded input length) index padding,
        getElem!_neg input index original, model]

theorem padded_canonical (input : Array Nat) (length : Nat) (canonical : Canonical input) :
    Canonical (padded input length) := by
  intro index bounded
  by_cases original : index < input.size
  · simp only [padded, Array.getElem_append, original, ↓reduceDIte]
    exact canonical index original
  · simp only [padded, Array.getElem_append, original, ↓reduceDIte, Array.getElem_replicate]
    exact (by decide : 0 < Q)

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.nextPower_go_lower
#print axioms LeanCrypto.Proofs.FFT.nextPower_lower
#print axioms LeanCrypto.Proofs.FFT.nextPower_go_exact
#print axioms LeanCrypto.Proofs.FFT.nextPower_go_target
#print axioms LeanCrypto.Proofs.FFT.nextPower_exact
#print axioms LeanCrypto.Proofs.FFT.padded_size
#print axioms LeanCrypto.Proofs.FFT.padded_lookup
#print axioms LeanCrypto.Proofs.FFT.padded_canonical

#print axioms LeanCrypto.Proofs.FFT.nextPowerGo_equation
