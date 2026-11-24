import LeanCryptoProofs.FFT.PolynomialModel
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

theorem dft_scale (length : Nat) (root scale : Fr) (input : Nat → Fr) (index : Nat) :
    dft length root (fun coefficient => scale * input coefficient) index =
      scale * dft length root input index := by
  simp only [dft, mul_assoc, Finset.mul_sum]

theorem dft_inverseDft (length : Nat) (root : Fr) (input : Nat → Fr) (index : Nat)
    (positive : 0 < length) (indexBound : index < length)
    (primitive : IsPrimitiveRoot root length) (sizeNonzero : (length : Fr) ≠ 0) :
    dft length root (inverseDft length root input) index = input index := by
  have inverse := inverseDft_dft length root⁻¹ input index positive indexBound primitive.inv sizeNonzero
  simp only [inverseDft, inv_inv] at inverse
  change dft length root (fun coefficient => (length : Fr)⁻¹ * dft length root⁻¹ input coefficient) index = input index
  rw [dft_scale]
  exact inverse

/-- IFFT constructs an ordinary coefficient polynomial whose evaluations
are the original domain vector, for every admitted size. -/
theorem ifft_polynomial_construct (input : Array Nat) (admitted : FFT.validSize input.size = true)
    (canonical : Canonical input) :
    ∃ output, FFT.ifft input = .ok output ∧ output.size = input.size ∧ Canonical output ∧
      ∀ index, index < input.size →
        (coeffPolynomial output).eval (domainRoot input.size ^ index) = fieldInput input index := by
  obtain ⟨output, built, size, bounded, values⟩ := ifft_construct input admitted canonical
  refine ⟨output, built, size, bounded, ?_⟩
  intro index indexBound
  rw [coeffPolynomial, finitePolynomial_dft, size]
  rw [dft_congr input.size (domainRoot input.size) (fieldInput output)
    (inverseDft input.size (domainRoot input.size) (fieldInput input)) values]
  apply dft_inverseDft input.size _ _ index _ indexBound
    (domainRoot_primitive input.size admitted) (domain_size_nonzero input.size admitted)
  have shape := (admitted_log_bound input.size admitted).2
  rw [← shape]
  exact pow_pos (by decide) _

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.dft_scale
#print axioms LeanCrypto.Proofs.FFT.dft_inverseDft
#print axioms LeanCrypto.Proofs.FFT.ifft_polynomial_construct
