import LeanCryptoProofs.FrModel
import LeanCryptoProofs.RootCertificate

namespace LeanCrypto.Proofs.BN254Fr

open LeanCrypto.Groth16

def constructedRoot (size : Nat) : Nat := FFT.powMod FFT.nqr ((Q - 1) / size)

theorem admitted_log_bound (size : Nat) (admitted : FFT.validSize size = true) :
    Nat.log2 size < 17 ∧ 2 ^ Nat.log2 size = size := by
  have requirements := admitted
  simp only [FFT.validSize, FFT.maximumSize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at requirements
  have positive : 0 < size := by omega
  have bound : size ≤ 65536 := by omega
  have exactPower : 2 ^ Nat.log2 size = size := by omega
  refine ⟨?_, exactPower⟩
  apply Nat.lt_of_not_ge
  intro excessive
  have powers := (Nat.le_log2 (Nat.ne_of_gt positive)).mp excessive
  change 131072 ≤ size at powers
  omega

theorem constructed_root_valid (size : Nat) (admitted : FFT.validSize size = true) :
    FFT.validRoot size (constructedRoot size) = true := by
  obtain ⟨bounded, exactPower⟩ := admitted_log_bound size admitted
  have checked := (List.all_eq_true.mp root_certificates) (Nat.log2 size) (List.mem_range.mpr bounded)
  simpa only [exactPower, constructedRoot, FFT.nqr] using checked

/-- Every admitted FFT length constructs an exact canonical root with full
order at its power-of-two length. There is no successful-return or roundtrip
premise: the complete fixed root family is certified by kernel reduction. -/
theorem rootOfUnity_constructed (size : Nat) (admitted : FFT.validSize size = true) :
    FFT.rootOfUnity size = .ok (constructedRoot size) ∧ constructedRoot size < Q ∧
    model (constructedRoot size) ^ size = 1 ∧
    (1 < size → model (constructedRoot size) ^ (size / 2) ≠ 1) ∧
    (Q - 1) % size = 0 := by
  have checked := constructed_root_valid size admitted
  have requirements := checked
  simp [FFT.validRoot] at requirements
  have nativePower : FFT.powMod (constructedRoot size) size = 1 := by omega
  have nativeHalf (higher : 1 < size) : FFT.powMod (constructedRoot size) (size / 2) ≠ 1 := by omega
  refine ⟨?_, powMod_bounded _ _, ?_, ?_, ?_⟩
  · unfold FFT.rootOfUnity
    change (if FFT.validRoot size (constructedRoot size) then (Except.ok (constructedRoot size) : Except String Nat) else Except.error _) = _
    rw [checked]
    rfl
  · have mathematical := model_powMod (constructedRoot size) size
    rw [nativePower] at mathematical
    simpa only [model, Nat.cast_one] using mathematical.symm
  · intro higher supposed
    have encoded : model (FFT.powMod (constructedRoot size) (size / 2)) = model 1 := by
      rw [model_powMod]
      simpa only [model, Nat.cast_one] using supposed
    exact nativeHalf higher (canonical_injective (powMod_bounded _ _) (by decide) encoded)
  · exact requirements.1.1.2

theorem power_size_admitted (log : Nat) (bounded : log < 17) : FFT.validSize (2 ^ log) = true := by
  have checked := (List.all_eq_true.mp root_certificates) log (List.mem_range.mpr bounded)
  cases valid : FFT.validSize (2 ^ log) with
  | true => rfl
  | false => simp [FFT.validRoot, valid] at checked

/-- Exact multiplicative order, not only a runtime root guard. -/
theorem constructed_root_exact_order (log : Nat) (bounded : log < 17) :
    orderOf (model (constructedRoot (2 ^ log))) = 2 ^ log := by
  have facts := rootOfUnity_constructed (2 ^ log) (power_size_admitted log bounded)
  cases log with
  | zero =>
    apply orderOf_eq_one_iff.mpr
    simpa only [pow_zero, pow_one] using facts.2.2.1
  | succ log =>
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime_pow
    · have larger : 1 < 2 ^ (log + 1) := by
        have positive : 0 < 2 ^ log := pow_pos (by decide) _
        rw [pow_succ]
        omega
      have half := facts.2.2.2.1 larger
      have halfSize : 2 ^ (log + 1) / 2 = 2 ^ log := by
        rw [pow_succ]
        exact Nat.mul_div_cancel _ (by decide)
      simpa only [halfSize] using half
    · exact facts.2.2.1

theorem admitted_root_exact_order (size : Nat) (admitted : FFT.validSize size = true) :
    orderOf (model (constructedRoot size)) = size := by
  obtain ⟨bounded, exactPower⟩ := admitted_log_bound size admitted
  have exactOrder := constructed_root_exact_order (Nat.log2 size) bounded
  simpa only [exactPower] using exactOrder

end LeanCrypto.Proofs.BN254Fr

#print axioms LeanCrypto.Proofs.BN254Fr.admitted_log_bound
#print axioms LeanCrypto.Proofs.BN254Fr.constructed_root_valid
#print axioms LeanCrypto.Proofs.BN254Fr.rootOfUnity_constructed
#print axioms LeanCrypto.Proofs.BN254Fr.power_size_admitted
#print axioms LeanCrypto.Proofs.BN254Fr.constructed_root_exact_order
#print axioms LeanCrypto.Proofs.BN254Fr.admitted_root_exact_order
