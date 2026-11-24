import TornadoProofs.Witness.MultiMux
import LeanCryptoProofs.BabyJubjub.NativeWindows
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
namespace TornadoProofs.Witness.PedersenWindows
open Primitive Field

def selectorIndex (s0 s1 s2 : Nat) : Nat := s0 + 2*s1 + 4*s2

theorem coordinate_selects_index (inputs : Array Nat) (coordinate s0 s1 s2 : Nat)
    (bit0 : s0 < 2) (bit1 : s1 < 2) (bit2 : s2 < 2) :
    model (coordinateValues inputs coordinate s0 s1 s2 (mul s1 s0))[8]! =
      model inputs[3 + coordinate*8 + selectorIndex s0 s1 s2]! := by
  interval_cases s0 <;> interval_cases s1 <;> interval_cases s2
  all_goals simp only [coordinateValues, selectorIndex, getElem!_def, List.getElem?_toArray,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero]
  all_goals simp only [model_sub, model_mul, model_add]
  all_goals simp only [model_ofNat]
  all_goals ring

theorem multiMux3_selects_models (inputs : Array Nat)
    (bit0 : inputs[0]! < 2) (bit1 : inputs[1]! < 2) (bit2 : inputs[2]! < 2) :
    model (multiMux3 inputs)[17]! = model inputs[3 + selectorIndex inputs[0]! inputs[1]! inputs[2]!]! ∧
      model (multiMux3 inputs)[18]! = model inputs[11 + selectorIndex inputs[0]! inputs[1]! inputs[2]!]! := by
  have first := congrArg (fun values : Array Nat => values[8]!) (coordinateAt_first inputs)
  have second := congrArg (fun values : Array Nat => values[8]!) (coordinateAt_second inputs)
  have firstEq : (multiMux3 inputs)[17]! =
      (coordinateValues inputs 0 inputs[0]! inputs[1]! inputs[2]! (mul inputs[1]! inputs[0]!))[8]! := by
    simpa [coordinateAt] using first
  have secondEq : (multiMux3 inputs)[18]! =
      (coordinateValues inputs 1 inputs[0]! inputs[1]! inputs[2]! (mul inputs[1]! inputs[0]!))[8]! := by
    simpa [coordinateAt] using second
  rw [firstEq, secondEq]
  exact ⟨by simpa using coordinate_selects_index inputs 0 _ _ _ bit0 bit1 bit2,
    by simpa using coordinate_selects_index inputs 1 _ _ _ bit0 bit1 bit2⟩

theorem multiMux3_selects_values (inputs : Array Nat) (bounded : Bounded inputs)
    (bit0 : inputs[0]! < 2) (bit1 : inputs[1]! < 2) (bit2 : inputs[2]! < 2) :
    (multiMux3 inputs)[17]! = inputs[3 + selectorIndex inputs[0]! inputs[1]! inputs[2]!]! ∧
      (multiMux3 inputs)[18]! = inputs[11 + selectorIndex inputs[0]! inputs[1]! inputs[2]!]! := by
  have equations := multiMux3_selects_models inputs bit0 bit1 bit2
  have outputBound := (multiMux3_shape inputs bounded).2
  exact ⟨model_injective_bounded _ _ (bounded_get _ outputBound 17) (bounded_get _ bounded _) equations.1,
    model_injective_bounded _ _ (bounded_get _ outputBound 18) (bounded_get _ bounded _) equations.2⟩

theorem actual_multiMux3_constructs_selection (inputs : Array Nat) (bounded : Bounded inputs)
    (bit0 : inputs[0]! < 2) (bit1 : inputs[1]! < 2) (bit2 : inputs[2]! < 2) :
    ∃ output, Tornado.Protocol.WitnessVM.primitiveValues "MultiMux3" inputs = .ok output ∧
      output[17]! = inputs[3 + selectorIndex inputs[0]! inputs[1]! inputs[2]!]! ∧
      output[18]! = inputs[11 + selectorIndex inputs[0]! inputs[1]! inputs[2]!]! := by
  obtain ⟨first, second⟩ := multiMux3_selects_values inputs bounded bit0 bit1 bit2
  exact ⟨multiMux3 inputs, multiMux3_construct inputs bit0 bit1 bit2, first, second⟩

theorem window4_sign_model (inputs : Array Nat) (bit : inputs[1]! < 2) :
    model (window4 inputs)[0]! = if inputs[1]! = 0 then model inputs[0]! else -model inputs[0]! := by
  have equation := window4_equations inputs
  change (2 * model inputs[0]!) * model inputs[1]! = model inputs[0]! - model (window4 inputs)[0]! at equation
  by_cases zero : inputs[1]! = 0
  · rw [if_pos zero]
    rw [zero, model_zero] at equation
    linear_combination equation
  · have one : inputs[1]! = 1 := by omega
    rw [if_neg zero]
    rw [one, model_one] at equation
    linear_combination equation

theorem actual_window4_constructs_sign (inputs : Array Nat) (bit : inputs[1]! < 2) :
    ∃ output, Tornado.Protocol.WitnessVM.primitiveValues "Window4" inputs = .ok output ∧
      model output[0]! = if inputs[1]! = 0 then model inputs[0]! else -model inputs[0]! :=
  ⟨window4 inputs, window4_construct inputs bit, window4_sign_model inputs bit⟩

theorem nativeNibble_from_bits (s0 s1 s2 sign : Nat)
    (bit0 : s0 < 2) (bit1 : s1 < 2) (bit2 : s2 < 2) (signBit : sign < 2) :
    LeanCrypto.Proofs.BabyJubjubWindows.nativeNibble (selectorIndex s0 s1 s2 + 8*sign) =
      if sign = 0 then ((selectorIndex s0 s1 s2 + 1 : Nat) : Int) else -((selectorIndex s0 s1 s2 + 1 : Nat) : Int) := by
  have low : selectorIndex s0 s1 s2 < 8 := by unfold selectorIndex; omega
  change (if selectorIndex s0 s1 s2 + 8*sign ≥ 8 then
      -(((selectorIndex s0 s1 s2 + 8*sign) % 8 + 1 : Nat) : Int)
    else (((selectorIndex s0 s1 s2 + 8*sign) % 8 + 1 : Nat) : Int)) = _
  interval_cases sign
  · simp only [mul_zero, add_zero]
    rw [if_neg (by omega), Nat.mod_eq_of_lt low]
    simp
  · have high : selectorIndex s0 s1 s2 + 8*1 ≥ 8 := by omega
    have remainder : (selectorIndex s0 s1 s2 + 8*1) % 8 = selectorIndex s0 s1 s2 := by omega
    simp only [if_pos high, remainder, Nat.one_ne_zero, ↓reduceIte]

def selectedWindow {G : Type} [AddCommGroup G] (base : G) (s0 s1 s2 sign : Nat) : G :=
  if sign = 0 then (selectorIndex s0 s1 s2 + 1) • base else -((selectorIndex s0 s1 s2 + 1) • base)

theorem selectedWindow_nativeNibble {G : Type} [AddCommGroup G] (base : G) (s0 s1 s2 sign : Nat)
    (bit0 : s0 < 2) (bit1 : s1 < 2) (bit2 : s2 < 2) (signBit : sign < 2) :
    selectedWindow base s0 s1 s2 sign =
      LeanCrypto.Proofs.BabyJubjubWindows.nativeNibble (selectorIndex s0 s1 s2 + 8*sign) • base := by
  rw [nativeNibble_from_bits s0 s1 s2 sign bit0 bit1 bit2 signBit]
  unfold selectedWindow
  split <;> simp only [natCast_zsmul, neg_zsmul]

def pointWindowValue {G : Type} [AddCommGroup G] (base : G) : List Int → G
  | [] => 0
  | digit :: rest => digit • base + pointWindowValue ((32 : Int) • base) rest

theorem pointWindowValue_scalar {G : Type} [AddCommGroup G] (base : G) (digits : List Int) :
    pointWindowValue base digits = LeanCrypto.Proofs.BabyJubjubWindows.windowValue digits • base := by
  induction digits generalizing base with
  | nil => simp only [pointWindowValue, LeanCrypto.Proofs.BabyJubjubWindows.windowValue, zero_zsmul]
  | cons digit rest ih =>
    rw [pointWindowValue, ih, LeanCrypto.Proofs.BabyJubjubWindows.windowValue, add_zsmul,
      mul_comm (32 : Int), mul_zsmul]

end TornadoProofs.Witness.PedersenWindows
#print axioms TornadoProofs.Witness.PedersenWindows.coordinate_selects_index
#print axioms TornadoProofs.Witness.PedersenWindows.multiMux3_selects_models
#print axioms TornadoProofs.Witness.PedersenWindows.multiMux3_selects_values
#print axioms TornadoProofs.Witness.PedersenWindows.actual_multiMux3_constructs_selection
#print axioms TornadoProofs.Witness.PedersenWindows.window4_sign_model
#print axioms TornadoProofs.Witness.PedersenWindows.actual_window4_constructs_sign
#print axioms TornadoProofs.Witness.PedersenWindows.nativeNibble_from_bits
#print axioms TornadoProofs.Witness.PedersenWindows.selectedWindow_nativeNibble
#print axioms TornadoProofs.Witness.PedersenWindows.pointWindowValue_scalar
