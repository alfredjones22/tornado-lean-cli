import LeanCryptoProofs.FFT.BitReverse
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

variable {A : Type} [Inhabited A]

def swapSource (values : Array A) (left right : Nat) : Array A :=
  (values.set! left values[right]!).set! right values[left]!

theorem swapSource_size (values : Array A) (left right : Nat) :
    (swapSource values left right).size = values.size := by simp [swapSource]

theorem swapSource_get (values : Array A) (left right index : Nat)
    (leftBound : left < values.size) (rightBound : right < values.size) (indexBound : index < values.size) :
    (swapSource values left right)[index]! =
      if index = left then values[right]! else if index = right then values[left]! else values[index]! := by
  by_cases atLeft : index = left
  · subst index
    by_cases same : left = right
    · subst right
      simp [swapSource, leftBound]
    · simp [swapSource, leftBound, rightBound, Ne.symm same]
  · by_cases atRight : index = right
    · subst index
      simp [swapSource, rightBound, atLeft]
    · simp [swapSource, indexBound, atLeft, atRight, Ne.symm atLeft, Ne.symm atRight]

def reversePrefix (input : Array A) (bits length : Nat) : Array A :=
  (List.range length).foldl (fun values index =>
    let partner := reverseNat bits index
    if index < partner then swapSource values index partner else values) input

theorem reversePrefix_succ (input : Array A) (bits length : Nat) :
    reversePrefix input bits (length + 1) =
      if length < reverseNat bits length then
        swapSource (reversePrefix input bits length) length (reverseNat bits length)
      else reversePrefix input bits length := by
  simp [reversePrefix, List.range_succ, List.foldl_append]

def ReverseInvariant (input : Array A) (bits length : Nat) (values : Array A) : Prop :=
  values.size = input.size ∧ ∀ index, index < input.size →
    values[index]! = if min index (reverseNat bits index) < length then input[reverseNat bits index]! else input[index]!

theorem reversePrefix_invariant (input : Array A) (bits length : Nat)
    (shape : input.size = 2 ^ bits) (lengthBound : length ≤ input.size) :
    ReverseInvariant input bits length (reversePrefix input bits length) := by
  induction length with
  | zero => simp [ReverseInvariant, reversePrefix]
  | succ length ih =>
    have previous := ih (by omega)
    obtain ⟨previousSize, previousValues⟩ := previous
    have currentBound : length < input.size := by omega
    have partnerBound : reverseNat bits length < input.size := by rw [shape]; exact reverseNat_bound _ _
    have partnerReverse : reverseNat bits (reverseNat bits length) = length :=
      reverseNat_involution bits length (by simpa only [shape] using currentBound)
    rw [reversePrefix_succ]
    by_cases swaps : length < reverseNat bits length
    · rw [if_pos swaps]
      constructor
      · simpa only [swapSource_size] using previousSize
      · intro index indexBound
        rw [swapSource_get _ length (reverseNat bits length) index
          (by omega) (by omega) (by omega)]
        by_cases atLeft : index = length
        · subst index
          simp only [↓reduceIte, previousValues _ partnerBound, partnerReverse]
          have partnerMinimum : min (reverseNat bits length) length = length := Nat.min_eq_right (by omega)
          rw [partnerMinimum]
          simp [Nat.min_eq_left (Nat.le_of_lt swaps)]
        by_cases atRight : index = reverseNat bits length
        · subst index
          rw [if_neg atLeft, if_pos rfl, previousValues _ currentBound, partnerReverse]
          simp [Nat.min_eq_left (Nat.le_of_lt swaps), Nat.min_eq_right (Nat.le_of_lt swaps)]
        · rw [if_neg atLeft, if_neg atRight, previousValues index indexBound]
          have different : reverseNat bits index ≠ length := by
            intro equal
            have reversed := congrArg (reverseNat bits) equal
            rw [reverseNat_involution bits index (by simpa only [shape] using indexBound)] at reversed
            exact atRight reversed
          have boundary : min index (reverseNat bits index) ≠ length := by
            rcases min_cases index (reverseNat bits index) with first | second
            · simpa only [first.1] using atLeft
            · simpa only [second.1] using different
          have cut : min index (reverseNat bits index) < length + 1 ↔
              min index (reverseNat bits index) < length := by omega
          simp only [cut]
    · rw [if_neg swaps]
      constructor
      · exact previousSize
      · intro index indexBound
        rw [previousValues index indexBound]
        by_cases old : min index (reverseNat bits index) < length
        · have current : min index (reverseNat bits index) < length + 1 := by omega
          simp only [old, current, ↓reduceIte]
        by_cases current : min index (reverseNat bits index) < length + 1
        · have boundary : min index (reverseNat bits index) = length := by omega
          have cases : index = length ∨ reverseNat bits index = length := by
            rcases min_cases index (reverseNat bits index) with first | second
            · exact Or.inl (first.1.symm.trans boundary)
            · exact Or.inr (second.1.symm.trans boundary)
          have fixed : reverseNat bits index = index := by
            rcases cases with equal | equal
            · subst index
              omega
            · have reversed := congrArg (reverseNat bits) equal
              rw [reverseNat_involution bits index (by simpa only [shape] using indexBound)] at reversed
              have : index = length := by omega
              omega
          simp only [fixed, ite_self]
        · simp only [old, current, ↓reduceIte]

theorem reversePrefix_permutation (input : Array A) (bits : Nat) (shape : input.size = 2 ^ bits) :
    (reversePrefix input bits input.size).size = input.size ∧
      ∀ index, index < input.size →
        (reversePrefix input bits input.size)[index]! = input[reverseNat bits index]! := by
  obtain ⟨sameSize, values⟩ := reversePrefix_invariant input bits input.size shape (by omega)
  refine ⟨sameSize, ?_⟩
  intro index bounded
  rw [values index bounded, if_pos (lt_of_le_of_lt (Nat.min_le_left _ _) bounded)]

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.swapSource_size
#print axioms LeanCrypto.Proofs.FFT.swapSource_get
#print axioms LeanCrypto.Proofs.FFT.reversePrefix_succ
#print axioms LeanCrypto.Proofs.FFT.reversePrefix_invariant
#print axioms LeanCrypto.Proofs.FFT.reversePrefix_permutation
