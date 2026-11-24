import LeanCrypto.Groth16.FFT
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16

def reverseState : Nat → Nat → Nat → MProd Nat Nat
  | 0, index, accumulator => ⟨index, accumulator⟩
  | steps + 1, index, accumulator =>
    reverseState steps (index / 2) (accumulator * 2 + index % 2)

def reverseNat (bits index : Nat) : Nat := (reverseState bits index 0).snd

theorem reverseState_fold (steps index accumulator : Nat) :
    (List.range steps).foldl (fun state _ =>
      (⟨state.fst / 2, state.snd * 2 + state.fst % 2⟩ : MProd Nat Nat)) ⟨index, accumulator⟩ =
      reverseState steps index accumulator := by
  induction steps generalizing index accumulator with
  | zero => rfl
  | succ steps ih =>
    simpa only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map, reverseState] using
      ih (index / 2) (accumulator * 2 + index % 2)

theorem native_reverseBits (index bits : Nat) : FFT.reverseBits index bits = reverseNat bits index := by
  have swapped := List.foldl_hom (fun state : MProd Nat Nat => (⟨state.snd, state.fst⟩ : MProd Nat Nat))
    (l := List.range bits) (init := ⟨0, index⟩)
    (g₁ := fun state _ => ⟨state.fst * 2 + state.snd % 2, state.snd / 2⟩)
    (g₂ := fun state _ => ⟨state.fst / 2, state.snd * 2 + state.fst % 2⟩)
    (by intros; rfl)
  have state := (congrArg MProd.snd swapped).symm.trans
    (congrArg MProd.snd (reverseState_fold bits index 0))
  simpa [FFT.reverseBits, reverseNat, List.range_eq_range'] using state

theorem reverseState_accumulator (bits index accumulator : Nat) :
    (reverseState bits index accumulator).snd =
      reverseNat bits index + accumulator * 2 ^ bits := by
  induction bits generalizing index accumulator with
  | zero => simp [reverseState, reverseNat]
  | succ bits ih =>
    change (reverseState bits (index / 2) (accumulator * 2 + index % 2)).snd =
      (reverseState bits (index / 2) (0 * 2 + index % 2)).snd + accumulator * 2 ^ (bits + 1)
    rw [ih (index / 2) (accumulator * 2 + index % 2), ih (index / 2) (0 * 2 + index % 2), pow_succ]
    ring

theorem reverseNat_zero (index : Nat) : reverseNat 0 index = 0 := rfl

theorem reverseNat_succ (bits index : Nat) :
    reverseNat (bits + 1) index = 2 ^ bits * (index % 2) + reverseNat bits (index / 2) := by
  change (reverseState bits (index / 2) (0 * 2 + index % 2)).snd = _
  rw [reverseState_accumulator]
  simp only [zero_mul, zero_add]
  ring

theorem reverseNat_bound (bits index : Nat) : reverseNat bits index < 2 ^ bits := by
  induction bits generalizing index with
  | zero => simp [reverseNat_zero]
  | succ bits ih =>
    rw [reverseNat_succ, pow_succ]
    have lower := ih (index / 2)
    have bitBound := Nat.mod_lt index (by decide : 0 < 2)
    rcases (by omega : index % 2 = 0 ∨ index % 2 = 1) with zero | one
    · rw [zero]
      omega
    · rw [one]
      omega

theorem reverseNat_even (bits index : Nat) :
    reverseNat (bits + 1) (2 * index) = reverseNat bits index := by
  rw [reverseNat_succ]
  have arithmetic : (2 * index) % 2 = 0 ∧ (2 * index) / 2 = index := by omega
  simp only [arithmetic.1, arithmetic.2, mul_zero, zero_add]

theorem reverseNat_odd (bits index : Nat) :
    reverseNat (bits + 1) (2 * index + 1) = reverseNat bits index + 2 ^ bits := by
  rw [reverseNat_succ]
  have arithmetic : (2 * index + 1) % 2 = 1 ∧ (2 * index + 1) / 2 = index := by omega
  rw [arithmetic.1, arithmetic.2, mul_one, Nat.add_comm]

theorem reverseNat_period (bits index multiple : Nat) :
    reverseNat bits (index + multiple * 2 ^ bits) = reverseNat bits index := by
  induction bits generalizing index multiple with
  | zero => rfl
  | succ bits ih =>
    have expansion : index + multiple * 2 ^ (bits + 1) = index + 2 * (multiple * 2 ^ bits) := by
      rw [pow_succ]
      ring
    rw [expansion, reverseNat_succ, reverseNat_succ]
    have bit : (index + 2 * (multiple * 2 ^ bits)) % 2 = index % 2 := by omega
    have quotient : (index + 2 * (multiple * 2 ^ bits)) / 2 = index / 2 + multiple * 2 ^ bits := by omega
    rw [bit, quotient, ih]

theorem reverseNat_high (bits index : Nat) :
    reverseNat (bits + 1) index = 2 * reverseNat bits index + (index / 2 ^ bits) % 2 := by
  induction bits generalizing index with
  | zero => simp [reverseNat_succ, reverseNat_zero]
  | succ bits ih =>
    rw [reverseNat_succ, ih, reverseNat_succ]
    have quotient : index / 2 / 2 ^ bits = index / 2 ^ (bits + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ]
      rw [Nat.mul_comm 2]
    rw [quotient, pow_succ]
    ring

theorem reverseNat_split_high (bits lower upper : Nat)
    (lowerBound : lower < 2 ^ bits) (upperBound : upper < 2) :
    reverseNat (bits + 1) (lower + upper * 2 ^ bits) =
      2 * reverseNat bits lower + upper := by
  rw [reverseNat_high, reverseNat_period,
    Nat.add_mul_div_right lower upper (pow_pos (by decide) _),
    Nat.div_eq_of_lt lowerBound, zero_add, Nat.mod_eq_of_lt upperBound]

theorem reverseNat_involution (bits index : Nat) (bounded : index < 2 ^ bits) :
    reverseNat bits (reverseNat bits index) = index := by
  induction bits generalizing index with
  | zero =>
    have : index = 0 := by simpa using bounded
    subst index
    rfl
  | succ bits ih =>
    have quotientBound : index / 2 < 2 ^ bits :=
      Nat.div_lt_of_lt_mul (by simpa only [pow_succ'] using bounded)
    calc
      reverseNat (bits + 1) (reverseNat (bits + 1) index) =
          reverseNat (bits + 1) (reverseNat bits (index / 2) + (index % 2) * 2 ^ bits) := by
        apply congrArg (reverseNat (bits + 1))
        rw [reverseNat_succ]
        ring
      _ = 2 * reverseNat bits (reverseNat bits (index / 2)) + index % 2 :=
        reverseNat_split_high bits _ _ (reverseNat_bound _ _) (Nat.mod_lt _ (by decide))
      _ = 2 * (index / 2) + index % 2 := by rw [ih _ quotientBound]
      _ = index := by have := Nat.mod_add_div index 2; omega

theorem reverseNat_injective (bits left right : Nat)
    (leftBound : left < 2 ^ bits) (rightBound : right < 2 ^ bits)
    (equal : reverseNat bits left = reverseNat bits right) : left = right := by
  have reversed := congrArg (reverseNat bits) equal
  simpa only [reverseNat_involution bits left leftBound, reverseNat_involution bits right rightBound] using reversed

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.reverseState_fold
#print axioms LeanCrypto.Proofs.FFT.native_reverseBits
#print axioms LeanCrypto.Proofs.FFT.reverseState_accumulator
#print axioms LeanCrypto.Proofs.FFT.reverseNat_zero
#print axioms LeanCrypto.Proofs.FFT.reverseNat_succ
#print axioms LeanCrypto.Proofs.FFT.reverseNat_bound
#print axioms LeanCrypto.Proofs.FFT.reverseNat_even
#print axioms LeanCrypto.Proofs.FFT.reverseNat_odd
#print axioms LeanCrypto.Proofs.FFT.reverseNat_period
#print axioms LeanCrypto.Proofs.FFT.reverseNat_high
#print axioms LeanCrypto.Proofs.FFT.reverseNat_split_high
#print axioms LeanCrypto.Proofs.FFT.reverseNat_involution
#print axioms LeanCrypto.Proofs.FFT.reverseNat_injective
