import LeanCryptoProofs.Fp6Model
set_option autoImplicit false
noncomputable section
namespace LeanCrypto.Proofs.BN254Fp6
open LeanCrypto.BN254.PairingField
noncomputable instance modelFintype : Fintype Field :=
  Fintype.ofEquiv (Fin 3 → Base) basis.equivFun.symm.toEquiv

theorem model_card : Fintype.card Field = BN254Fp.P ^ 6 := by
  rw [Fintype.card_congr basis.equivFun.toEquiv, Fintype.card_fun, Fintype.card_fin,
    BN254Fp2.model_card, ← pow_mul]

/-- Proof-side binary evaluator over the actual native multiplication. -/
def nativePowLoop (base : Fp6) (exponent : Nat) (accumulator : Fp6) : Fp6 :=
  if zero : exponent = 0 then accumulator
  else nativePowLoop (base.mul base) (exponent / 2)
    (if exponent % 2 = 1 then accumulator.mul base else accumulator)
termination_by exponent
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

def nativePow (base : Fp6) (exponent : Nat) := nativePowLoop base exponent Fp6.one

theorem model_nativePowLoop (base accumulator : Fp6) (exponent : Nat) :
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
theorem model_nativePow (value : Fp6) (exponent : Nat) :
    model (nativePow value exponent) = model value ^ exponent := by
  simpa only [nativePow, model_one, one_mul] using model_nativePowLoop value Fp6.one exponent

theorem field_fermat (value : Field) (nonzero : value ≠ 0) :
    value ^ (BN254Fp.P ^ 6 - 1) = 1 := by
  classical
  have units := pow_card_eq_one (x := Units.mk0 value nonzero)
  have values := congrArg (fun unit : Fieldˣ => (unit : Field)) units
  simpa [Fintype.card_units, model_card] using values


set_option maxRecDepth 16384
set_option maxHeartbeats 0 in
theorem v_square_certificate :
    nativePow Fp6.v ((BN254Fp.P ^ 6 - 1) / 2) != Fp6.one := by
  decide +kernel

theorem v_nonzero : model Fp6.v ≠ 0 := by
  intro zero
  have equal : Fp6.v = Fp6.zero := model_injective (zero.trans model_zero.symm)
  have middle := congrArg (fun value : Fp6 => BN254Fp2.model value.c1) equal
  simp [Fp6.v, Fp6.zero] at middle

theorem v_not_square (value : Field) : value ^ 2 ≠ model Fp6.v := by
  intro square
  have nonzero : value ≠ 0 := by
    intro zero
    rw [zero, zero_pow (by decide)] at square
    exact v_nonzero square.symm
  have division : 2 * ((BN254Fp.P ^ 6 - 1) / 2) = BN254Fp.P ^ 6 - 1 := by decide +kernel
  have cannot : model Fp6.v ^ ((BN254Fp.P ^ 6 - 1) / 2) ≠ 1 := by
    rw [← model_nativePow]
    intro equal
    have nativeEqual : nativePow Fp6.v ((BN254Fp.P ^ 6 - 1) / 2) = Fp6.one :=
      model_injective (equal.trans model_one.symm)
    have impossible := v_square_certificate
    rw [nativeEqual] at impossible
    change false = true at impossible
    cases impossible
  apply cannot
  rw [← square, ← pow_mul, division]
  exact field_fermat value nonzero

end LeanCrypto.Proofs.BN254Fp6
#print axioms LeanCrypto.Proofs.BN254Fp6.model_card
#print axioms LeanCrypto.Proofs.BN254Fp6.model_nativePowLoop
#print axioms LeanCrypto.Proofs.BN254Fp6.model_nativePow
#print axioms LeanCrypto.Proofs.BN254Fp6.field_fermat
#print axioms LeanCrypto.Proofs.BN254Fp6.v_square_certificate
#print axioms LeanCrypto.Proofs.BN254Fp6.v_nonzero
#print axioms LeanCrypto.Proofs.BN254Fp6.v_not_square
