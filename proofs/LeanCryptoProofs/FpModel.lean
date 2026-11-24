import LeanCrypto.BN254.G1
import Mathlib.Algebra.Field.ZMod

/-! Mathematical representation of the actual native BN254 Fp operations.
This proof-only module is separate from the dependency-free runtime package.
Primality is needed only for inverse completeness, not the ring operations. -/

namespace LeanCrypto.Proofs.BN254Fp

open LeanCrypto.BN254.G1

abbrev P := basePrime

instance : NeZero P := ⟨by decide⟩

def model (value : Fp) : ZMod P := value.val

def encode (value : ZMod P) : Fp := Fp.ofNat value.val

theorem native_ext {left right : Fp} (same : left.val = right.val) : left = right := by
  cases left
  cases right
  cases same
  rfl

@[simp]
theorem model_ofNat (value : Nat) : model (Fp.ofNat value) = (value : ZMod P) := by
  exact ZMod.natCast_mod value P

@[simp]
theorem model_zero : model Fp.zero = 0 := by simp [Fp.zero]
@[simp]
theorem model_one : model Fp.one = 1 := by simp [Fp.one]

@[simp]
theorem model_val (value : Fp) : (model value).val = value.val :=
  ZMod.val_natCast_of_lt value.bounded

theorem model_injective : Function.Injective model := by
  intro left right same
  apply native_ext
  have values := congrArg ZMod.val same
  simpa only [model_val] using values

@[simp]
theorem encode_model (value : Fp) : encode (model value) = value := by
  apply native_ext
  simp [encode, Fp.ofNat, Nat.mod_eq_of_lt value.bounded]

@[simp]
theorem model_encode (value : ZMod P) : model (encode value) = value := by
  rw [encode, model_ofNat, ZMod.natCast_zmod_val]

@[simp]
theorem model_add (left right : Fp) : model (left.add right) = model left + model right := by
  rw [Fp.add, model_ofNat]
  exact Nat.cast_add left.val right.val

@[simp]
theorem model_mul (left right : Fp) : model (left.mul right) = model left * model right := by
  rw [Fp.mul, model_ofNat]
  exact Nat.cast_mul left.val right.val

@[simp]
theorem model_neg (value : Fp) : model value.neg = -model value := by
  rw [Fp.neg, model_ofNat]
  change ((P - value.val : Nat) : ZMod P) = -(value.val : ZMod P)
  rw [Nat.cast_sub value.bounded.le]
  simp

@[simp]
theorem model_sub (left right : Fp) : model (left.sub right) = model left - model right := by
  simp [Fp.sub, sub_eq_add_neg]

theorem model_beq (left right : Fp) : (left == right) = true ↔ model left = model right := by
  constructor
  · intro same
    have values : left.val = right.val := (beq_iff_eq).mp same
    exact congrArg (fun n : Nat => (n : ZMod P)) values
  · intro same
    have equal := model_injective same
    subst right
    change (left.val == left.val) = true
    simp

theorem native_add_assoc (a b c : Fp) : (a.add b).add c = a.add (b.add c) := by
  apply model_injective
  simp [add_assoc]

theorem native_mul_assoc (a b c : Fp) : (a.mul b).mul c = a.mul (b.mul c) := by
  apply model_injective
  simp [mul_assoc]

theorem native_left_distrib (a b c : Fp) : a.mul (b.add c) = (a.mul b).add (a.mul c) := by
  apply model_injective
  simp [mul_add]

theorem native_add_neg (a : Fp) : a.add a.neg = Fp.zero := by
  apply model_injective
  simp

/-- The invariant proves square-and-multiply for every exponent and initial
accumulator, over the actual total native implementation. -/
theorem model_powLoop (base accumulator : Fp) (exponent : Nat) :
    model (Fp.powLoop base exponent accumulator) = model accumulator * model base ^ exponent := by
  induction exponent using Nat.strong_induction_on generalizing base accumulator with
  | h exponent ih =>
    rw [Fp.powLoop]
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
theorem model_pow (value : Fp) (exponent : Nat) :
    model (value.pow exponent) = model value ^ exponent := by
  simpa only [Fp.pow, model_one, one_mul] using model_powLoop value Fp.one exponent

/-- A finite multiplicative group gives Fermat's equation without trusting a
native primality test. The actual prime certificate can instantiate Fact. -/
theorem model_fermat [Fact P.Prime] (value : ZMod P) (nonzero : value ≠ 0) :
    value ^ (P - 1) = 1 := by
  have units := pow_card_eq_one (x := Units.mk0 value nonzero)
  have values := congrArg (fun unit : (ZMod P)ˣ => (unit : ZMod P)) units
  simpa [Fintype.card_units, ZMod.card] using values

/-- Every nonzero native field value constructs its inverse by the actual
p-2 exponentiation, and that value is the mathematical field inverse. -/
theorem inverse_complete [Fact P.Prime] (value : Fp) (nonzero : model value ≠ 0) :
    value.inverse = .ok (encode ((model value)⁻¹)) := by
  let candidate := value.pow (P - 2)
  have product : model value * model candidate = 1 := by
    rw [show model candidate = model value ^ (P - 2) from model_pow value (P - 2)]
    rw [← pow_succ']
    have exponent : P - 2 + 1 = P - 1 := by decide
    rw [exponent]
    exact model_fermat (model value) nonzero
  have inverse : model candidate = (model value)⁻¹ := by
    apply mul_left_cancel₀ nonzero
    rw [product, mul_inv_cancel₀ nonzero]
  have nativeProduct : (value.mul candidate == Fp.one) = true := by
    apply (model_beq _ _).2
    simpa only [model_mul, model_one] using product
  have nativeNonzero : (value == Fp.zero) = false := by
    cases equality : value == Fp.zero with
    | false => rfl
    | true =>
      have zero := (model_beq value Fp.zero).1 equality
      exact False.elim (nonzero (by simpa only [model_zero] using zero))
  have nativeInverse : candidate = encode ((model value)⁻¹) :=
    model_injective (by simpa only [model_encode] using inverse)
  simp only [Fp.inverse, nativeNonzero, Bool.false_eq_true, ↓reduceIte]
  change (if value.mul candidate == Fp.one then (Except.ok candidate : Except String Fp)
    else .error "BN254 Fp inverse check failed.") = .ok (encode ((model value)⁻¹))
  rw [nativeProduct]
  simpa only [↓reduceIte] using
    congrArg (fun native : Fp => (Except.ok native : Except String Fp)) nativeInverse

theorem inverse_total [Fact P.Prime] (value : Fp) :
    value.inverse = if model value = 0 then .error "BN254 Fp zero has no inverse."
      else .ok (encode ((model value)⁻¹)) := by
  by_cases zero : model value = 0
  · have nativeZero : value = Fp.zero := model_injective (by simpa only [model_zero] using zero)
    subst value
    simp only [model_zero, ↓reduceIte]
    rfl
  · rw [if_neg zero]
    exact inverse_complete value zero

theorem native_mul_inverse [Fact P.Prime] (value : Fp) (nonzero : model value ≠ 0) :
    value.mul (encode ((model value)⁻¹)) = Fp.one := by
  apply model_injective
  simp only [model_mul, model_encode, model_one]
  exact mul_inv_cancel₀ nonzero

theorem affine_onCurve_iff (point : Affine) : point.onCurve = true ↔
    model point.y ^ 2 = model point.x ^ 3 + 3 := by
  rw [Affine.onCurve, model_beq]
  simp only [model_mul, model_add, model_ofNat]
  simp only [pow_succ, pow_zero, one_mul, Nat.cast_ofNat]

end LeanCrypto.Proofs.BN254Fp

#print axioms LeanCrypto.Proofs.BN254Fp.native_ext
#print axioms LeanCrypto.Proofs.BN254Fp.model_ofNat
#print axioms LeanCrypto.Proofs.BN254Fp.model_zero
#print axioms LeanCrypto.Proofs.BN254Fp.model_one
#print axioms LeanCrypto.Proofs.BN254Fp.model_val
#print axioms LeanCrypto.Proofs.BN254Fp.model_injective
#print axioms LeanCrypto.Proofs.BN254Fp.encode_model
#print axioms LeanCrypto.Proofs.BN254Fp.model_encode
#print axioms LeanCrypto.Proofs.BN254Fp.model_add
#print axioms LeanCrypto.Proofs.BN254Fp.model_mul
#print axioms LeanCrypto.Proofs.BN254Fp.model_neg
#print axioms LeanCrypto.Proofs.BN254Fp.model_sub
#print axioms LeanCrypto.Proofs.BN254Fp.model_beq
#print axioms LeanCrypto.Proofs.BN254Fp.native_add_assoc
#print axioms LeanCrypto.Proofs.BN254Fp.native_mul_assoc
#print axioms LeanCrypto.Proofs.BN254Fp.native_left_distrib
#print axioms LeanCrypto.Proofs.BN254Fp.native_add_neg

#print axioms LeanCrypto.Proofs.BN254Fp.model_powLoop
#print axioms LeanCrypto.Proofs.BN254Fp.model_pow
#print axioms LeanCrypto.Proofs.BN254Fp.model_fermat
#print axioms LeanCrypto.Proofs.BN254Fp.inverse_complete

#print axioms LeanCrypto.Proofs.BN254Fp.inverse_total
#print axioms LeanCrypto.Proofs.BN254Fp.native_mul_inverse
#print axioms LeanCrypto.Proofs.BN254Fp.affine_onCurve_iff
