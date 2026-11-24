import LeanCryptoProofs.Fp2Model
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Fp2
open LeanCrypto.BN254.G2

/-- Proof-side binary evaluator over the actual native multiplication. -/
def nativePowLoop (base : Fp2) (exponent : Nat) (accumulator : Fp2) : Fp2 :=
  if zero : exponent = 0 then accumulator
  else nativePowLoop (base.mul base) (exponent / 2)
    (if exponent % 2 = 1 then accumulator.mul base else accumulator)
termination_by exponent
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

def nativePow (base : Fp2) (exponent : Nat) := nativePowLoop base exponent Fp2.one

theorem model_nativePowLoop (base accumulator : Fp2) (exponent : Nat) :
    model (nativePowLoop base exponent accumulator) = model accumulator * model base ^ exponent := by
  induction exponent using Nat.strong_induction_on generalizing base accumulator with
  | h exponent ih =>
    rw [nativePowLoop]
    split
    · rename_i zero
      simp [zero]
    · rename_i nonzero
      have smaller : exponent / 2 < exponent :=
        Nat.div_lt_self (Nat.pos_of_ne_zero nonzero) (by decide)
      rw [ih (exponent / 2) smaller]
      by_cases odd : exponent % 2 = 1
      · simp only [odd, ↓reduceIte, model_mul]
        rw [← pow_two, ← pow_mul, mul_assoc, ← pow_succ']
        have divide := Nat.mod_add_div exponent 2
        have equal : 2 * (exponent / 2) + 1 = exponent := by omega
        rw [equal]
      · have remainder : exponent % 2 = 0 := by
          have bound := Nat.mod_lt exponent (by decide : 0 < 2)
          omega
        simp only [odd, ↓reduceIte, model_mul]
        rw [← pow_two, ← pow_mul]
        have divide := Nat.mod_add_div exponent 2
        have equal : 2 * (exponent / 2) = exponent := by omega
        rw [equal]

@[simp]
theorem model_nativePow (value : Fp2) (exponent : Nat) :
    model (nativePow value exponent) = model value ^ exponent := by
  simpa only [nativePow, model_one, one_mul] using model_nativePowLoop value Fp2.one exponent

theorem field_fermat (value : Field) (nonzero : value ≠ 0) :
    value ^ (BN254Fp.P ^ 2 - 1) = 1 := by
  classical
  have units := pow_card_eq_one (x := Units.mk0 value nonzero)
  have values := congrArg (fun unit : Fieldˣ => (unit : Field)) units
  simpa [Fintype.card_units, model_card] using values

set_option maxRecDepth 8192
set_option maxHeartbeats 0 in
theorem nonresidue_cube_certificate :
    nativePow (Fp2.ofNats 9 1) ((BN254Fp.P ^ 2 - 1) / 3) != Fp2.one := by
  decide +kernel

theorem nonresidue_not_cube (value : Field) :
    value ^ 3 ≠ model (Fp2.ofNats 9 1) := by
  intro cube
  have xiNonzero : model (Fp2.ofNats 9 1) ≠ 0 := by decide +kernel
  have nonzero : value ≠ 0 := by
    intro zero
    rw [zero, zero_pow (by decide)] at cube
    exact xiNonzero cube.symm
  have division : 3 * ((BN254Fp.P ^ 2 - 1) / 3) = BN254Fp.P ^ 2 - 1 := by decide +kernel
  have cannot : model (Fp2.ofNats 9 1) ^ ((BN254Fp.P ^ 2 - 1) / 3) ≠ 1 := by
    rw [← model_nativePow]
    intro equal
    have nativeEqual : nativePow (Fp2.ofNats 9 1) ((BN254Fp.P ^ 2 - 1) / 3) = Fp2.one :=
      model_injective (equal.trans model_one.symm)
    have impossible := nonresidue_cube_certificate
    rw [nativeEqual] at impossible
    change false = true at impossible
    cases impossible
  apply cannot
  rw [← cube, ← pow_mul, division]
  exact field_fermat value nonzero

end LeanCrypto.Proofs.BN254Fp2

#print axioms LeanCrypto.Proofs.BN254Fp2.model_nativePowLoop
#print axioms LeanCrypto.Proofs.BN254Fp2.model_nativePow
#print axioms LeanCrypto.Proofs.BN254Fp2.field_fermat
#print axioms LeanCrypto.Proofs.BN254Fp2.nonresidue_cube_certificate
#print axioms LeanCrypto.Proofs.BN254Fp2.nonresidue_not_cube
