import LeanCryptoProofs.FrModel

namespace LeanCrypto.Proofs.BN254Fr

open LeanCrypto.Groth16

@[simp]
theorem butterfly_size (values : Array Nat) (left right twiddle : Nat) :
    (FFT.butterfly values left right twiddle).size = values.size := by
  simp [FFT.butterfly]

theorem butterfly_left (values : Array Nat) (left right twiddle : Nat)
    (leftBound : left < values.size) (different : left ≠ right) :
    (FFT.butterfly values left right twiddle)[left]'(by simpa using leftBound) =
      FFT.add values[left] (FFT.mul values[right]! twiddle) := by
  simp [FFT.butterfly, Ne.symm different, leftBound]

theorem butterfly_right (values : Array Nat) (left right twiddle : Nat)
    (rightBound : right < values.size) :
    (FFT.butterfly values left right twiddle)[right]'(by simpa using rightBound) =
      FFT.sub values[left]! (FFT.mul values[right] twiddle) := by
  simp [FFT.butterfly, rightBound]

theorem butterfly_unrelated (values : Array Nat) (left right twiddle index : Nat)
    (bounded : index < values.size) (notLeft : index ≠ left) (notRight : index ≠ right) :
    (FFT.butterfly values left right twiddle)[index]'(by simpa using bounded) = values[index] := by
  simp [FFT.butterfly, bounded, Ne.symm notLeft, Ne.symm notRight]

theorem butterfly_field_meaning (values : Array Nat) (left right twiddle : Nat)
    (leftBound : left < values.size) (rightBound : right < values.size) (different : left ≠ right) :
    model ((FFT.butterfly values left right twiddle)[left]'(by simpa using leftBound)) =
        model values[left] + model values[right] * model twiddle ∧
    model ((FFT.butterfly values left right twiddle)[right]'(by simpa using rightBound)) =
        model values[left] - model values[right] * model twiddle := by
  rw [butterfly_left values left right twiddle leftBound different,
    butterfly_right values left right twiddle rightBound]
  simp [leftBound, rightBound]

theorem butterfly_preserves_canonical (values : Array Nat) (left right twiddle : Nat)
    (canonical : ∀ index, (bounded : index < values.size) → values[index] < Q) :
    ∀ index, (bounded : index < (FFT.butterfly values left right twiddle).size) →
      (FFT.butterfly values left right twiddle)[index] < Q := by
  intro index bounded
  have originalBound : index < values.size := by simpa using bounded
  by_cases atRight : index = right
  · subst index
    rw [butterfly_right values left right twiddle originalBound]
    exact Nat.mod_lt _ (by decide)
  by_cases atLeft : index = left
  · subst index
    rw [butterfly_left values left right twiddle originalBound atRight]
    exact Nat.mod_lt _ (by decide)
  rw [butterfly_unrelated values left right twiddle index originalBound atLeft atRight]
  exact canonical index originalBound

end LeanCrypto.Proofs.BN254Fr

#print axioms LeanCrypto.Proofs.BN254Fr.butterfly_size
#print axioms LeanCrypto.Proofs.BN254Fr.butterfly_left
#print axioms LeanCrypto.Proofs.BN254Fr.butterfly_right
#print axioms LeanCrypto.Proofs.BN254Fr.butterfly_unrelated
#print axioms LeanCrypto.Proofs.BN254Fr.butterfly_field_meaning
#print axioms LeanCrypto.Proofs.BN254Fr.butterfly_preserves_canonical
