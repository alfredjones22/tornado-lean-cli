import LeanCryptoProofs.FFT.NativeTransform
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Proofs.BN254Fr

noncomputable def finitePolynomial (length : Nat) (coefficients : Nat → Fr) : Polynomial Fr :=
  ∑ index ∈ Finset.range length, Polynomial.monomial index (coefficients index)

noncomputable def coeffPolynomial (input : Array Nat) : Polynomial Fr :=
  finitePolynomial input.size (fieldInput input)

theorem finitePolynomial_coeff (length : Nat) (coefficients : Nat → Fr) (index : Nat) :
    (finitePolynomial length coefficients).coeff index =
      if index < length then coefficients index else 0 := by
  classical
  simp [finitePolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]

theorem finitePolynomial_degree (length : Nat) (coefficients : Nat → Fr) :
    (finitePolynomial length coefficients).degree < length := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro index bounded
  rw [finitePolynomial_coeff, if_neg (Nat.not_lt_of_ge bounded)]

theorem finitePolynomial_natDegree (length : Nat) (coefficients : Nat → Fr) (positive : 0 < length) :
    (finitePolynomial length coefficients).natDegree < length := by
  by_cases zero : finitePolynomial length coefficients = 0
  · simp only [zero, Polynomial.natDegree_zero]
    exact positive
  · exact (Polynomial.natDegree_lt_iff_degree_lt zero).2 (finitePolynomial_degree length coefficients)

theorem finitePolynomial_eval (length : Nat) (coefficients : Nat → Fr) (value : Fr) :
    (finitePolynomial length coefficients).eval value =
      ∑ index ∈ Finset.range length, coefficients index * value ^ index := by
  simp only [finitePolynomial, Polynomial.eval_finset_sum, Polynomial.eval_monomial]

theorem finitePolynomial_dft (length : Nat) (coefficients : Nat → Fr) (root : Fr) (index : Nat) :
    (finitePolynomial length coefficients).eval (root ^ index) = dft length root coefficients index := by
  rw [finitePolynomial_eval]
  simp only [dft, ← pow_mul]

theorem polynomial_dft (polynomial : Polynomial Fr) (length : Nat) (root : Fr) (index : Nat)
    (degreeBound : polynomial.natDegree < length) :
    polynomial.eval (root ^ index) = dft length root polynomial.coeff index := by
  rw [Polynomial.eval_eq_sum_range' degreeBound]
  simp only [dft, ← pow_mul]

theorem finitePolynomial_reconstruct (polynomial : Polynomial Fr) (length : Nat)
    (degreeBound : polynomial.natDegree < length) :
    finitePolynomial length polynomial.coeff = polynomial := by
  exact (polynomial.as_sum_range' length degreeBound).symm

theorem coeffPolynomial_coeff (input : Array Nat) (index : Nat) :
    (coeffPolynomial input).coeff index = fieldInput input index := by
  rw [coeffPolynomial, finitePolynomial_coeff]
  split
  · rfl
  · rename_i outside
    simp [fieldInput, getElem!_neg input index outside, model]

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.finitePolynomial_coeff
#print axioms LeanCrypto.Proofs.FFT.finitePolynomial_degree
#print axioms LeanCrypto.Proofs.FFT.finitePolynomial_natDegree
#print axioms LeanCrypto.Proofs.FFT.finitePolynomial_eval
#print axioms LeanCrypto.Proofs.FFT.finitePolynomial_dft
#print axioms LeanCrypto.Proofs.FFT.polynomial_dft
#print axioms LeanCrypto.Proofs.FFT.finitePolynomial_reconstruct
#print axioms LeanCrypto.Proofs.FFT.coeffPolynomial_coeff
