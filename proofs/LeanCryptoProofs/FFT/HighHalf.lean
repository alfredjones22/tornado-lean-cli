import LeanCryptoProofs.FFT.PolynomialModel
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

theorem polynomial_eq_of_domain_eval (length : Nat) (root : Fr)
    (primitive : IsPrimitiveRoot root length) (positive : 0 < length)
    (sizeNonzero : (length : Fr) ≠ 0) (left right : Polynomial Fr)
    (leftDegree : left.natDegree < length) (rightDegree : right.natDegree < length)
    (evaluations : ∀ index, index < length → left.eval (root ^ index) = right.eval (root ^ index)) :
    left = right := by
  have dfts (index : Nat) (bounded : index < length) :
      dft length root left.coeff index = dft length root right.coeff index := by
    rw [← polynomial_dft left length root index leftDegree,
      ← polynomial_dft right length root index rightDegree]
    exact evaluations index bounded
  apply Polynomial.ext
  intro index
  by_cases bounded : index < length
  · rw [← inverseDft_dft length root left.coeff index positive bounded primitive sizeNonzero,
      ← inverseDft_dft length root right.coeff index positive bounded primitive sizeNonzero]
    unfold inverseDft
    rw [dft_congr _ _ _ _ dfts]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : left.natDegree < index),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : right.natDegree < index)]

noncomputable def lowHalf (length : Nat) (polynomial : Polynomial Fr) : Polynomial Fr :=
  finitePolynomial length polynomial.coeff

noncomputable def highHalf (length : Nat) (polynomial : Polynomial Fr) : Polynomial Fr :=
  finitePolynomial length (fun index => polynomial.coeff (length + index))

theorem high_low_split (length : Nat) (polynomial : Polynomial Fr)
    (degreeBound : polynomial.natDegree < length + length) :
    polynomial = lowHalf length polynomial + Polynomial.X ^ length * highHalf length polynomial := by
  apply Polynomial.ext
  intro index
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', lowHalf, highHalf,
    finitePolynomial_coeff, finitePolynomial_coeff]
  by_cases lower : index < length
  · simp only [lower, ↓reduceIte, Nat.not_le_of_lt lower]
    simp
  · have upper : length ≤ index := by omega
    rw [if_neg lower, if_pos upper, zero_add]
    split
    · congr 1
      omega
    · rename_i beyond
      have zero := Polynomial.coeff_eq_zero_of_natDegree_lt (show polynomial.natDegree < index by omega)
      exact zero

/-- The high half is the vanishing-polynomial quotient, derived from the
independent domain row equations and the degree bound on C. -/
theorem highHalf_quotient (length : Nat) (root : Fr)
    (primitive : IsPrimitiveRoot root length) (positive : 0 < length)
    (sizeNonzero : (length : Fr) ≠ 0) (product c : Polynomial Fr)
    (productDegree : product.natDegree < length + length) (cDegree : c.natDegree < length)
    (rows : ∀ index, index < length → product.eval (root ^ index) = c.eval (root ^ index)) :
    product - c = highHalf length product * (Polynomial.X ^ length - 1) := by
  let low := lowHalf length product
  let high := highHalf length product
  have lowDegree : low.natDegree < length := finitePolynomial_natDegree _ _ positive
  have highDegree : high.natDegree < length := finitePolynomial_natDegree _ _ positive
  have sumDegree : (low + high).natDegree < length :=
    lt_of_le_of_lt (Polynomial.natDegree_add_le low high) (max_lt lowDegree highDegree)
  have split := high_low_split length product productDegree
  have domain (index : Nat) (bounded : index < length) :
      (low + high).eval (root ^ index) = c.eval (root ^ index) := by
    have power : (root ^ index) ^ length = 1 := by
      rw [← pow_mul, Nat.mul_comm index length, pow_mul, primitive.pow_eq_one, one_pow]
    have row := rows index bounded
    rw [split, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, power, one_mul] at row
    simpa only [Polynomial.eval_add] using row
  have equals : low + high = c :=
    polynomial_eq_of_domain_eval length root primitive positive sizeNonzero _ _ sumDegree cDegree domain
  conv_lhs => rw [split]
  change low + Polynomial.X ^ length * high - c = high * (Polynomial.X ^ length - 1)
  rw [← equals]
  ring

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.polynomial_eq_of_domain_eval
#print axioms LeanCrypto.Proofs.FFT.high_low_split
#print axioms LeanCrypto.Proofs.FFT.highHalf_quotient
