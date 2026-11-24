import LeanCryptoProofs.FFT.HighHalf
open Lean Elab Term Meta
elab "actualFFTTrim" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Groth16.FFT `LeanCrypto.Groth16.FFT.trimZeros)
elab "actualFFTTrimEquation" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Groth16.FFT `LeanCrypto.Groth16.FFT.trimZeros.eq_def)

set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

abbrev nativeTrim (values : Array Nat) : Array Nat := actualFFTTrim values

theorem nativeTrim_equation (values : Array Nat) :
    nativeTrim values = if values.isEmpty then values
      else if values[values.size - 1]! == 0 then nativeTrim values.pop else values :=
  actualFFTTrimEquation values

theorem pop_zero_polynomial (values : Array Nat)
    (lastZero : values[values.size - 1]! = 0) :
    coeffPolynomial values.pop = coeffPolynomial values := by
  apply Polynomial.ext
  intro index
  rw [coeffPolynomial_coeff, coeffPolynomial_coeff]
  unfold fieldInput
  by_cases before : index < values.pop.size
  · rw [getElem!_pos values.pop index before,
      getElem!_pos values index (by have := Array.size_pop (xs := values); omega)]
    simp only [Array.getElem_pop]
  · rw [getElem!_neg values.pop index before]
    by_cases bounded : index < values.size
    · have last : index = values.size - 1 := by
        have := Array.size_pop (xs := values)
        omega
      rw [last, lastZero]
      rfl
    · rw [getElem!_neg values index bounded]

theorem pop_canonical (values : Array Nat) (canonical : Canonical values) :
    Canonical values.pop := by
  intro index bounded
  simp only [Array.getElem_pop]
  exact canonical index (by have := Array.size_pop (xs := values); omega)

theorem nativeTrim_preserves (values : Array Nat) (canonical : Canonical values) :
    (nativeTrim values).size ≤ values.size ∧ Canonical (nativeTrim values) ∧
      coeffPolynomial (nativeTrim values) = coeffPolynomial values := by
  generalize size : values.size = length
  induction length using Nat.strong_induction_on generalizing values with
  | h length ih =>
    rw [nativeTrim_equation]
    split
    · exact ⟨Nat.le_of_eq size, canonical, rfl⟩
    · rename_i notEmpty
      split
      · rename_i zero
        have lastZero : values[values.size - 1]! = 0 := beq_iff_eq.mp zero
        have positive : 0 < values.size := by
          simp only [Array.isEmpty, decide_eq_true_eq] at notEmpty
          omega
        have smaller : values.pop.size < length := by
          rw [Array.size_pop]
          omega
        obtain ⟨bounded, canon, same⟩ := ih values.pop.size smaller values.pop
          (pop_canonical values canonical) rfl
        refine ⟨?_, canon, same.trans (pop_zero_polynomial values lastZero)⟩
        have := Array.size_pop (xs := values)
        omega
      · exact ⟨Nat.le_of_eq size, canonical, rfl⟩

theorem nativeTrim_zero_tail_size (values : Array Nat) (canonical : Canonical values)
    (positive : 0 < values.size) (lastZero : values[values.size - 1]! = 0) :
    (nativeTrim values).size ≤ values.size - 1 := by
  have nonempty : values.isEmpty = false := by simp only [Array.isEmpty, decide_eq_false_iff_not]; omega
  rw [nativeTrim_equation]
  simp only [nonempty, Bool.false_eq_true, ↓reduceIte, lastZero, beq_self_eq_true]
  have bounded := (nativeTrim_preserves values.pop (pop_canonical values canonical)).1
  simpa only [Array.size_pop] using bounded

theorem extract_highHalf (values : Array Nat) (length : Nat)
    (shape : values.size = length + length) :
    coeffPolynomial (values.extract length values.size) = highHalf length (coeffPolynomial values) := by
  have size : (values.extract length values.size).size = length := by simp only [Array.size_extract, min_self, shape]; omega
  apply Polynomial.ext
  intro index
  rw [coeffPolynomial_coeff, highHalf, finitePolynomial_coeff]
  by_cases bounded : index < length
  · rw [if_pos bounded, coeffPolynomial_coeff]
    unfold fieldInput
    rw [getElem!_pos (values.extract length values.size) index (by rw [size]; exact bounded),
      getElem!_pos values (length + index) (by omega)]
    simp only [Array.getElem_extract]
  · rw [if_neg bounded]
    simp only [fieldInput, getElem!_neg (values.extract length values.size) index (by rw [size]; exact bounded)]
    rfl

theorem extract_canonical (values : Array Nat) (start stop : Nat) (canonical : Canonical values) :
    Canonical (values.extract start stop) := by
  intro index bounded
  simp only [Array.getElem_extract]
  exact canonical (start + index) (by
    have : index < min stop values.size - start := by simpa only [Array.size_extract] using bounded
    omega)

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.nativeTrim_equation
#print axioms LeanCrypto.Proofs.FFT.pop_zero_polynomial
#print axioms LeanCrypto.Proofs.FFT.pop_canonical
#print axioms LeanCrypto.Proofs.FFT.nativeTrim_preserves
#print axioms LeanCrypto.Proofs.FFT.nativeTrim_zero_tail_size
#print axioms LeanCrypto.Proofs.FFT.extract_highHalf
#print axioms LeanCrypto.Proofs.FFT.extract_canonical
