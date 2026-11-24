import Tornado.Protocol.WitnessVM
import LeanCryptoProofs.CertifiedFields

/-! Model of the actual private witness field operators. Private-name terms
only reference the existing declarations; all equalities are kernel checked.
The runtime power helper shares canonical total FFT.powMod. -/
open Lean Elab Term Meta
elab "vmNativeAdd" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore `Tornado.Protocol.WitnessVM `Tornado.Protocol.WitnessVM.fadd)
elab "vmNativeSub" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore `Tornado.Protocol.WitnessVM `Tornado.Protocol.WitnessVM.fsub)
elab "vmNativeMul" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore `Tornado.Protocol.WitnessVM `Tornado.Protocol.WitnessVM.fmul)
elab "vmNativePow" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore `Tornado.Protocol.WitnessVM `Tornado.Protocol.WitnessVM.powMod)
elab "vmNativeInv" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore `Tornado.Protocol.WitnessVM `Tornado.Protocol.WitnessVM.finv)

set_option autoImplicit false
namespace TornadoProofs.Witness.Field

open LeanCrypto.Groth16
abbrev q := Tornado.Protocol.Groth16R1CS.scalarPrime
abbrev model := LeanCrypto.Proofs.BN254Fr.model
abbrev Model := ZMod LeanCrypto.Proofs.BN254Fr.Q
abbrev add (x y : Nat) : Nat := vmNativeAdd x y
abbrev sub (x y : Nat) : Nat := vmNativeSub x y
abbrev mul (x y : Nat) : Nat := vmNativeMul x y
abbrev pow (x exponent : Nat) : Nat := vmNativePow x exponent
abbrev inverse (x : Nat) : Except String Nat := vmNativeInv x

theorem add_eq (x y : Nat) : add x y = FFT.add x y := rfl
theorem sub_eq (x y : Nat) : sub x y = FFT.sub x y := rfl
theorem mul_eq (x y : Nat) : mul x y = FFT.mul x y := rfl
theorem pow_eq (x exponent : Nat) : pow x exponent = FFT.powMod x exponent := rfl

@[simp]
theorem model_add (x y : Nat) : model (add x y) = model x + model y :=
  LeanCrypto.Proofs.BN254Fr.model_add x y
@[simp]
theorem model_sub (x y : Nat) : model (sub x y) = model x - model y :=
  LeanCrypto.Proofs.BN254Fr.model_sub x y
@[simp]
theorem model_mul (x y : Nat) : model (mul x y) = model x * model y :=
  LeanCrypto.Proofs.BN254Fr.model_mul x y
@[simp]
theorem model_pow (x exponent : Nat) : model (pow x exponent) = model x ^ exponent :=
  LeanCrypto.Proofs.BN254Fr.model_powMod x exponent

@[simp]
theorem model_zero : model 0 = 0 := by simp [model, LeanCrypto.Proofs.BN254Fr.model]
@[simp]
theorem model_one : model 1 = 1 := by simp [model, LeanCrypto.Proofs.BN254Fr.model]
@[simp]
theorem model_ofNat (n : Nat) : model n = (n : Model) := rfl

theorem add_bounded (x y : Nat) : add x y < q := Nat.mod_lt _ (by decide)
theorem sub_bounded (x y : Nat) : sub x y < q := Nat.mod_lt _ (by decide)
theorem mul_bounded (x y : Nat) : mul x y < q := Nat.mod_lt _ (by decide)
theorem pow_bounded (x exponent : Nat) : pow x exponent < q :=
  LeanCrypto.Proofs.BN254Fr.powMod_bounded x exponent

/-- A reference body identical to the native helper; error messages are the
circuit-specific ones rather than the FFT wrapper's diagnostics. -/
def inverseBody (x : Nat) : Except String Nat := do
  if x % q == 0 then throw "Circuit point operation divides by zero."
  let candidate := FFT.powMod x (q - 2)
  if FFT.mul x candidate != 1 then throw "Circuit point denominator is not invertible."
  return candidate

theorem inverse_body (x : Nat) : inverse x = inverseBody x := rfl

private theorem inverse_transport (x candidate : Nat)
    (known : FFT.inverse x = .ok candidate) : inverse x = .ok candidate := by
  rw [inverse_body]
  cases zero : x % q == 0 with
  | true => simp [FFT.inverse, show FFT.modulus = q from rfl, zero] at known
  | false =>
    cases product : FFT.mul x (FFT.powMod x (q - 2)) == 1 with
    | false => simp [FFT.inverse, show FFT.modulus = q from rfl, zero, product] at known
    | true =>
      have equal : FFT.powMod x (q - 2) = candidate := by
        simpa only [FFT.inverse, show FFT.modulus = q from rfl, zero, product,
          Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] using known
      have good : FFT.mul x candidate = 1 := (beq_iff_eq).mp (by simpa only [equal] using product)
      simp [inverseBody, zero, equal, good, bind, Except.bind, pure, Except.pure]

/-- Closed numerical primality discharges the actual exponentiation/product
check for every independent nonzero modeled denominator. -/
theorem inverse_construct (x : Nat) (nonzero : model x ≠ 0) :
    inverse x = .ok ((model x)⁻¹).val :=
  inverse_transport x _ (LeanCrypto.Proofs.BN254Fr.inverse_complete x nonzero)

theorem inverse_value_bounded (x : Nat) : ((model x)⁻¹).val < q := ZMod.val_lt _

@[simp]
theorem model_inverse_value (x : Nat) : model ((model x)⁻¹).val = (model x)⁻¹ :=
  ZMod.natCast_zmod_val _

theorem model_injective_bounded (x y : Nat) (xb : x < q) (yb : y < q)
    (equal : model x = model y) : x = y :=
  LeanCrypto.Proofs.BN254Fr.canonical_injective xb yb equal

theorem model_zero_iff (x : Nat) : model x = 0 ↔ x % q = 0 :=
  LeanCrypto.Proofs.BN254Fr.model_zero_iff x

/-- The symbolic public DAG uses the same actual Fermat power. For nonzero
inputs it is constructively the independently defined field inverse. -/
theorem power_inverse (x : Nat) (nonzero : model x ≠ 0) :
    FFT.powMod x (q-2) = ((model x)⁻¹).val := by
  have success := LeanCrypto.Proofs.BN254Fr.inverse_complete x nonzero
  unfold FFT.inverse at success
  split at success
  · cases success
  · dsimp only at success
    split at success
    · exact Except.ok.inj success
    · cases success

end TornadoProofs.Witness.Field

#print axioms TornadoProofs.Witness.Field.add_eq
#print axioms TornadoProofs.Witness.Field.sub_eq
#print axioms TornadoProofs.Witness.Field.mul_eq
#print axioms TornadoProofs.Witness.Field.pow_eq
#print axioms TornadoProofs.Witness.Field.model_add
#print axioms TornadoProofs.Witness.Field.model_sub
#print axioms TornadoProofs.Witness.Field.model_mul
#print axioms TornadoProofs.Witness.Field.model_pow
#print axioms TornadoProofs.Witness.Field.model_zero
#print axioms TornadoProofs.Witness.Field.model_one
#print axioms TornadoProofs.Witness.Field.model_ofNat
#print axioms TornadoProofs.Witness.Field.add_bounded
#print axioms TornadoProofs.Witness.Field.sub_bounded
#print axioms TornadoProofs.Witness.Field.mul_bounded
#print axioms TornadoProofs.Witness.Field.pow_bounded
#print axioms TornadoProofs.Witness.Field.inverse_body
#print axioms TornadoProofs.Witness.Field.inverse_transport
#print axioms TornadoProofs.Witness.Field.inverse_construct
#print axioms TornadoProofs.Witness.Field.inverse_value_bounded
#print axioms TornadoProofs.Witness.Field.model_inverse_value
#print axioms TornadoProofs.Witness.Field.model_injective_bounded
#print axioms TornadoProofs.Witness.Field.model_zero_iff

#print axioms TornadoProofs.Witness.Field.power_inverse
