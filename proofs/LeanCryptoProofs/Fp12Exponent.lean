import LeanCryptoProofs.Fp12Model
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Fp12
open LeanCrypto.BN254.PairingField
noncomputable instance modelFintype : Fintype Field :=
  Fintype.ofEquiv (Base × Base) (QuadraticAlgebra.equivProd (BN254Fp6.model Fp6.v) 0).symm

theorem model_card : Fintype.card Field = BN254Fp.P ^ 12 := by
  rw [Fintype.card_congr (QuadraticAlgebra.equivProd (BN254Fp6.model Fp6.v) 0),
    Fintype.card_prod, BN254Fp6.model_card, ← pow_two, ← pow_mul]

theorem model_powLoop (base accumulator : Fp12) (exponent : Nat) :
    model (Fp12.powLoop base exponent accumulator) = model accumulator * model base ^ exponent := by
  induction exponent using Nat.strong_induction_on generalizing base accumulator with
  | h exponent ih =>
    rw [Fp12.powLoop]
    split
    · rename_i zero
      simp [zero]
    · rename_i nonzero
      have smaller : exponent / 2 < exponent :=
        Nat.div_lt_self (Nat.pos_of_ne_zero nonzero) (by decide)
      rw [ih (exponent / 2) smaller]
      by_cases odd : exponent % 2 = 1
      · simp only [odd, ↓reduceIte, model_mul, model_square]
        rw [← pow_mul, mul_assoc, ← pow_succ']
        have divide := Nat.mod_add_div exponent 2
        have equal : 2 * (exponent / 2) + 1 = exponent := by omega
        rw [equal]
      · have remainder : exponent % 2 = 0 := by
          have bound := Nat.mod_lt exponent (by decide : 0 < 2)
          omega
        simp only [odd, ↓reduceIte, model_square]
        rw [← pow_mul]
        have divide := Nat.mod_add_div exponent 2
        have equal : 2 * (exponent / 2) = exponent := by omega
        rw [equal]

@[simp]
theorem model_pow (value : Fp12) (exponent : Nat) :
    model (Fp12.pow value exponent) = model value ^ exponent := by
  simpa only [Fp12.pow, model_one, one_mul] using model_powLoop value Fp12.one exponent

theorem field_fermat (value : Field) (nonzero : value ≠ 0) :
    value ^ (BN254Fp.P ^ 12 - 1) = 1 := by
  classical
  have units := pow_card_eq_one (x := Units.mk0 value nonzero)
  have values := congrArg (fun unit : Fieldˣ => (unit : Field)) units
  simpa [Fintype.card_units, model_card] using values


end LeanCrypto.Proofs.BN254Fp12
#print axioms LeanCrypto.Proofs.BN254Fp12.model_card
#print axioms LeanCrypto.Proofs.BN254Fp12.model_powLoop
#print axioms LeanCrypto.Proofs.BN254Fp12.model_pow
#print axioms LeanCrypto.Proofs.BN254Fp12.field_fermat
