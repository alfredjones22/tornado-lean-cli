import LeanCrypto.Pedersen
import LeanCryptoProofs.CertifiedFields

open Lean Elab Term Meta
elab "pedersenFieldPrivate" name:ident : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Pedersen name.getId)
elab "unfoldPedersenPowLoop" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic1 fun goal => goal.deltaTarget (· ==
    mkPrivateNameCore `LeanCrypto.Pedersen `LeanCrypto.powModLoop)

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjubField
open LeanCrypto.Proofs.BN254Fr
abbrev nativePrime : Nat := pedersenFieldPrivate LeanCrypto.fieldPrime
abbrev nativeAdd (x y : Nat) : Nat := (pedersenFieldPrivate LeanCrypto.fadd) x y
abbrev nativeSub (x y : Nat) : Nat := (pedersenFieldPrivate LeanCrypto.fsub) x y
abbrev nativeMul (x y : Nat) : Nat := (pedersenFieldPrivate LeanCrypto.fmul) x y
abbrev nativePowLoop (x n accumulator : Nat) : Nat :=
  (pedersenFieldPrivate LeanCrypto.powModLoop) x n accumulator
abbrev nativePow (x n : Nat) : Nat := (pedersenFieldPrivate LeanCrypto.powMod) x n
abbrev nativeInverse (x : Nat) : Option Nat := (pedersenFieldPrivate LeanCrypto.finv) x

theorem native_modulus : nativePrime = Q := rfl

theorem native_add_model (x y : Nat) : model (nativeAdd x y) = model x + model y := model_add x y

theorem native_sub_model (x y : Nat) : model (nativeSub x y) = model x - model y := model_sub x y

theorem native_mul_model (x y : Nat) : model (nativeMul x y) = model x * model y := model_mul x y

theorem nativePowLoop_eq (x n accumulator : Nat) :
    nativePowLoop x n accumulator = LeanCrypto.Groth16.FFT.powModLoop x n accumulator := by
  induction n using Nat.strong_induction_on generalizing x accumulator with
  | h n ih =>
    unfold nativePowLoop
    rw [(pedersenFieldPrivate LeanCrypto.powModLoop.eq_def) x n accumulator, LeanCrypto.Groth16.FFT.powModLoop]
    simp only [beq_iff_eq]
    split
    · rfl
    · rename_i nonzero
      have smaller : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero nonzero) (by decide)
      exact ih (n / 2) smaller _ _

theorem nativePow_eq (x n : Nat) : nativePow x n = LeanCrypto.Groth16.FFT.powMod x n :=
  nativePowLoop_eq _ _ _

theorem native_pow_model (x n : Nat) : model (nativePow x n) = model x ^ n := by
  rw [nativePow_eq]
  exact model_powMod x n

theorem native_inverse_construct (x : Nat) (nonzero : model x ≠ 0) :
    nativeInverse x = some ((model x)⁻¹).val := by
  have nonzeroNat : x % Q ≠ 0 := (model_zero_iff x).not.mp nonzero
  have inverse := inverse_complete x nonzero
  have pow : LeanCrypto.Groth16.FFT.powMod x (Q - 2) = ((model x)⁻¹).val := by
    unfold LeanCrypto.Groth16.FFT.inverse at inverse
    simp only [show (x % Q == 0) = false from beq_eq_false_iff_ne.mpr nonzeroNat,
      Bool.false_eq_true, ↓reduceIte] at inverse
    split at inverse
    · exact Except.ok.inj inverse
    · cases inverse
  change (if x % Q == 0 then none else some (nativePow x (Q - 2))) = _
  rw [if_neg (by simpa only [beq_iff_eq] using nonzeroNat), nativePow_eq, pow]

end LeanCrypto.Proofs.BabyJubjubField
#print axioms LeanCrypto.Proofs.BabyJubjubField.native_modulus
#print axioms LeanCrypto.Proofs.BabyJubjubField.native_add_model
#print axioms LeanCrypto.Proofs.BabyJubjubField.native_sub_model
#print axioms LeanCrypto.Proofs.BabyJubjubField.native_mul_model
#print axioms LeanCrypto.Proofs.BabyJubjubField.nativePowLoop_eq
#print axioms LeanCrypto.Proofs.BabyJubjubField.nativePow_eq
#print axioms LeanCrypto.Proofs.BabyJubjubField.native_pow_model
#print axioms LeanCrypto.Proofs.BabyJubjubField.native_inverse_construct
