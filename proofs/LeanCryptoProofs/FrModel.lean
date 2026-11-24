import LeanCrypto.Groth16.FFT
import Mathlib.Algebra.Field.ZMod

/-! Mathematical representation of the actual native Fr operations and
binary exponentiation. This proof-only module does not add Mathlib to the
runtime library. Inverse completeness has an explicit primality hypothesis. -/

namespace LeanCrypto.Proofs.BN254Fr

open LeanCrypto.Groth16

abbrev Q := FFT.modulus

instance : NeZero Q := ⟨by decide⟩

def model (value : Nat) : ZMod Q := value

@[simp]
theorem model_mod (value : Nat) : model (value % Q) = model value :=
  ZMod.natCast_mod value Q

@[simp]
theorem model_add (left right : Nat) : model (FFT.add left right) = model left + model right := by
  rw [FFT.add, model_mod]
  exact Nat.cast_add left right

@[simp]
theorem model_mul (left right : Nat) : model (FFT.mul left right) = model left * model right := by
  rw [FFT.mul, model_mod]
  exact Nat.cast_mul left right

@[simp]
theorem model_sub (left right : Nat) : model (FFT.sub left right) = model left - model right := by
  rw [FFT.sub, model_mod]
  change ((left + Q - right % Q : Nat) : ZMod Q) = (left : ZMod Q) - right
  have bound := Nat.mod_lt right (show 0 < Q by decide)
  rw [Nat.cast_sub (show right % Q ≤ left + Q by omega), Nat.cast_add, ZMod.natCast_self,
    ZMod.natCast_mod]
  simp

theorem canonical_injective {left right : Nat} (leftBound : left < Q) (rightBound : right < Q)
    (equal : model left = model right) : left = right := by
  have values := congrArg ZMod.val equal
  simpa only [model, ZMod.val_natCast_of_lt leftBound, ZMod.val_natCast_of_lt rightBound] using values

@[simp]
theorem model_val (value : ZMod Q) : model value.val = value := ZMod.natCast_zmod_val value

theorem model_zero_iff (value : Nat) : model value = 0 ↔ value % Q = 0 := by
  constructor
  · intro zero
    have values := congrArg ZMod.val zero
    simpa only [model, ZMod.val_natCast, ZMod.val_zero] using values
  · intro zero
    rw [← model_mod value, zero]
    rfl

theorem model_powModLoop (base result exponent : Nat) :
    model (FFT.powModLoop base exponent result) = model result * model base ^ exponent := by
  induction exponent using Nat.strong_induction_on generalizing base result with
  | h exponent ih =>
    rw [FFT.powModLoop]
    split
    · rename_i zero
      simp [zero, model]
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
theorem model_powMod (base exponent : Nat) :
    model (FFT.powMod base exponent) = model base ^ exponent := by
  change model (FFT.powModLoop (base % Q) exponent 1) = model base ^ exponent
  rw [model_powModLoop, model_mod]
  change (1 : ZMod Q) * model base ^ exponent = model base ^ exponent
  exact one_mul _

theorem powModLoop_bounded (base result exponent : Nat) (canonical : result < Q) :
    FFT.powModLoop base exponent result < Q := by
  induction exponent using Nat.strong_induction_on generalizing base result with
  | h exponent ih =>
    rw [FFT.powModLoop]
    split
    · exact canonical
    · rename_i nonzero
      apply ih (exponent / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero nonzero) (by decide))
      split
      · exact Nat.mod_lt _ (by decide)
      · exact canonical

theorem powMod_bounded (base exponent : Nat) : FFT.powMod base exponent < Q :=
  powModLoop_bounded (base % Q) 1 exponent (by decide)

theorem model_fermat [Fact Q.Prime] (value : ZMod Q) (nonzero : value ≠ 0) :
    value ^ (Q - 1) = 1 := by
  have units := pow_card_eq_one (x := Units.mk0 value nonzero)
  have values := congrArg (fun unit : (ZMod Q)ˣ => (unit : ZMod Q)) units
  simpa [Fintype.card_units, ZMod.card] using values

/-- Nonzero modular inputs construct the canonical mathematical inverse with
the actual modulus-minus-two code; no successful-return premise is assumed. -/
theorem inverse_complete [Fact Q.Prime] (value : Nat) (nonzero : model value ≠ 0) :
    FFT.inverse value = .ok ((model value)⁻¹).val := by
  let candidate := FFT.powMod value (Q - 2)
  have product : model value * model candidate = 1 := by
    rw [show model candidate = model value ^ (Q - 2) from model_powMod value (Q - 2), ← pow_succ']
    have exponent : Q - 2 + 1 = Q - 1 := by decide
    rw [exponent]
    exact model_fermat (model value) nonzero
  have inverse : model candidate = (model value)⁻¹ := by
    apply mul_left_cancel₀ nonzero
    rw [product, mul_inv_cancel₀ nonzero]
  have canonicalCandidate : candidate = ((model value)⁻¹).val := by
    have values := congrArg ZMod.val inverse
    change (candidate : ZMod Q).val = ((model value)⁻¹).val at values
    rw [ZMod.val_natCast_of_lt (powMod_bounded value (Q - 2))] at values
    exact values
  have nativeProduct : FFT.mul value candidate = 1 := by
    apply canonical_injective (Nat.mod_lt _ (by decide)) (by decide)
    change model (FFT.mul value candidate) = model 1
    rw [model_mul]
    simpa only [model, Nat.cast_one] using product
  have nativeNonzero : value % Q ≠ 0 := fun zero => nonzero ((model_zero_iff value).2 zero)
  have nonzeroTest : (value % Q == 0) = false := beq_eq_false_iff_ne.mpr nativeNonzero
  simp only [FFT.inverse, nonzeroTest, Bool.false_eq_true, ↓reduceIte]
  change (if FFT.mul value candidate == 1 then (Except.ok candidate : Except String Nat)
    else .error "Fr inverse check failed.") = .ok ((model value)⁻¹).val
  simp only [nativeProduct, beq_self_eq_true, ↓reduceIte]
  exact congrArg (fun native : Nat => (Except.ok native : Except String Nat)) canonicalCandidate

theorem inverse_total [Fact Q.Prime] (value : Nat) :
    FFT.inverse value = if model value = 0 then .error "Fr zero has no inverse."
      else .ok ((model value)⁻¹).val := by
  by_cases zero : model value = 0
  · have nativeZero := (model_zero_iff value).1 zero
    simp only [FFT.inverse, nativeZero, beq_self_eq_true, ↓reduceIte, zero]
  · rw [if_neg zero]
    exact inverse_complete value zero

end LeanCrypto.Proofs.BN254Fr

#print axioms LeanCrypto.Proofs.BN254Fr.model_mod
#print axioms LeanCrypto.Proofs.BN254Fr.model_add
#print axioms LeanCrypto.Proofs.BN254Fr.model_mul
#print axioms LeanCrypto.Proofs.BN254Fr.model_sub
#print axioms LeanCrypto.Proofs.BN254Fr.canonical_injective
#print axioms LeanCrypto.Proofs.BN254Fr.model_val
#print axioms LeanCrypto.Proofs.BN254Fr.model_zero_iff
#print axioms LeanCrypto.Proofs.BN254Fr.model_powModLoop
#print axioms LeanCrypto.Proofs.BN254Fr.model_powMod
#print axioms LeanCrypto.Proofs.BN254Fr.powModLoop_bounded
#print axioms LeanCrypto.Proofs.BN254Fr.powMod_bounded
#print axioms LeanCrypto.Proofs.BN254Fr.model_fermat
#print axioms LeanCrypto.Proofs.BN254Fr.inverse_complete
#print axioms LeanCrypto.Proofs.BN254Fr.inverse_total
