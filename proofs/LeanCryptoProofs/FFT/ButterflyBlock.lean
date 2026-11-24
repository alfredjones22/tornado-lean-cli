import LeanCryptoProofs.FFT.FFTSource
import LeanCryptoProofs.FFT.DFT
import LeanCryptoProofs.ButterflyModel

set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

def Canonical (values : Array Nat) : Prop :=
  ∀ index, (bounded : index < values.size) → values[index] < Q

theorem butterfly_get_model (values : Array Nat) (left right twiddle index : Nat)
    (leftBound : left < values.size) (rightBound : right < values.size)
    (different : left ≠ right) (indexBound : index < values.size) :
    model (FFT.butterfly values left right twiddle)[index]! =
      if index = left then model values[left]! + model values[right]! * model twiddle
      else if index = right then model values[left]! - model values[right]! * model twiddle
      else model values[index]! := by
  have meaning := butterfly_field_meaning values left right twiddle leftBound rightBound different
  by_cases atLeft : index = left
  · subst index
    simpa [leftBound, rightBound] using meaning.1
  by_cases atRight : index = right
  · subst index
    simpa [leftBound, rightBound, atLeft] using meaning.2
  · have unchanged := butterfly_unrelated values left right twiddle index indexBound atLeft atRight
    simpa [indexBound, atLeft, atRight] using congrArg model unchanged

def blockPrefix (input : Array Nat) (start half step length : Nat) : MProd (Array Nat) Nat :=
  (List.range length).foldl (fun state index =>
    ⟨FFT.butterfly state.fst (start + index) (start + index + half) state.snd,
      FFT.mul state.snd step⟩) ⟨input, 1⟩

theorem blockPrefix_succ (input : Array Nat) (start half step length : Nat) :
    blockPrefix input start half step (length + 1) =
      let previous := blockPrefix input start half step length
      ⟨FFT.butterfly previous.fst (start + length) (start + length + half) previous.snd,
        FFT.mul previous.snd step⟩ := by
  simp [blockPrefix, List.range_succ, List.foldl_append]

def leftButterfly (input : Array Nat) (start half step index : Nat) : Fr :=
  model input[start + index]! + model input[start + index + half]! * model step ^ index

def rightButterfly (input : Array Nat) (start half step index : Nat) : Fr :=
  model input[start + index]! - model input[start + index + half]! * model step ^ index

def BlockInvariant (input : Array Nat) (start half step length : Nat)
    (state : MProd (Array Nat) Nat) : Prop :=
  state.fst.size = input.size ∧ model state.snd = model step ^ length ∧
  (∀ index, index < half →
    (model state.fst[start + index]! =
      if index < length then leftButterfly input start half step index else model input[start + index]!) ∧
    (model state.fst[start + index + half]! =
      if index < length then rightButterfly input start half step index else model input[start + index + half]!)) ∧
  (∀ index, index < input.size → (index < start ∨ start + half + half ≤ index) →
    state.fst[index]! = input[index]!) ∧ Canonical state.fst

theorem blockPrefix_invariant (input : Array Nat) (start half step length : Nat)
    (room : start + half + half ≤ input.size) (lengthBound : length ≤ half) (canonical : Canonical input) :
    BlockInvariant input start half step length (blockPrefix input start half step length) := by
  induction length with
  | zero =>
    simp [blockPrefix, BlockInvariant, canonical, model]
  | succ length ih =>
    obtain ⟨previousSize, previousTwiddle, previousPairs, previousOther, previousCanonical⟩ := ih (by omega)
    have leftBound : start + length < (blockPrefix input start half step length).fst.size := by omega
    have rightBound : start + length + half < (blockPrefix input start half step length).fst.size := by omega
    have different : start + length ≠ start + length + half := by omega
    have oldLeft := (previousPairs length (by omega)).1
    have oldRight := (previousPairs length (by omega)).2
    simp only [lt_self_iff_false, ↓reduceIte] at oldLeft oldRight
    rw [blockPrefix_succ]
    refine ⟨by simpa only [butterfly_size] using previousSize, ?_, ?_, ?_, ?_⟩
    · simp only [model_mul, previousTwiddle, pow_succ]
    · intro index indexBound
      have indexLeft : start + index < (blockPrefix input start half step length).fst.size := by omega
      have indexRight : start + index + half < (blockPrefix input start half step length).fst.size := by omega
      constructor
      · rw [butterfly_get_model _ _ _ _ _ leftBound rightBound different indexLeft]
        by_cases same : index = length
        · subst index
          rw [if_pos rfl, oldLeft, oldRight, previousTwiddle, if_pos (by omega)]
          rfl
        · have notLeft : start + index ≠ start + length := by omega
          have notRight : start + index ≠ start + length + half := by omega
          have cut : index < length + 1 ↔ index < length := by omega
          rw [if_neg notLeft, if_neg notRight, (previousPairs index indexBound).1]
          simp only [cut]
      · rw [butterfly_get_model _ _ _ _ _ leftBound rightBound different indexRight]
        have notLeft : start + index + half ≠ start + length := by omega
        rw [if_neg notLeft]
        by_cases same : index = length
        · subst index
          rw [if_pos rfl, oldLeft, oldRight, previousTwiddle, if_pos (by omega)]
          rfl
        · have notRight : start + index + half ≠ start + length + half := by omega
          have cut : index < length + 1 ↔ index < length := by omega
          rw [if_neg notRight, (previousPairs index indexBound).2]
          simp only [cut]
    · intro index indexBound outside
      have notLeft : index ≠ start + length := by omega
      have notRight : index ≠ start + length + half := by omega
      have unchanged := butterfly_unrelated (blockPrefix input start half step length).fst
        (start + length) (start + length + half) (blockPrefix input start half step length).snd
        index (by omega) notLeft notRight
      simpa [show index < (blockPrefix input start half step length).fst.size by omega] using
        unchanged.trans (by simpa [show index < (blockPrefix input start half step length).fst.size by omega]
          using previousOther index indexBound outside)
    · exact butterfly_preserves_canonical _ _ _ _ previousCanonical

theorem blockPrefix_complete (input : Array Nat) (start half step : Nat)
    (room : start + half + half ≤ input.size) (canonical : Canonical input) :
    (blockPrefix input start half step half).fst.size = input.size ∧
    (∀ index, index < half →
      model (blockPrefix input start half step half).fst[start + index]! = leftButterfly input start half step index ∧
      model (blockPrefix input start half step half).fst[start + index + half]! = rightButterfly input start half step index) ∧
    (∀ index, index < input.size → (index < start ∨ start + half + half ≤ index) →
      (blockPrefix input start half step half).fst[index]! = input[index]!) ∧
    Canonical (blockPrefix input start half step half).fst := by
  obtain ⟨sameSize, _, pairs, other, bounded⟩ := blockPrefix_invariant input start half step half room (by omega) canonical
  refine ⟨sameSize, ?_, other, bounded⟩
  intro index indexBound
  simpa only [if_pos indexBound] using pairs index indexBound

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.butterfly_get_model
#print axioms LeanCrypto.Proofs.FFT.blockPrefix_succ
#print axioms LeanCrypto.Proofs.FFT.blockPrefix_invariant
#print axioms LeanCrypto.Proofs.FFT.blockPrefix_complete
