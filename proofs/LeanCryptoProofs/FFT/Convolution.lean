import LeanCryptoProofs.FFT.PolynomialModel
import LeanCryptoProofs.FFT.Padding
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

/-- The actual FFT convolution constructs the ordinary polynomial product.
The returned array retains the runtime's next-power-of-two padding. -/
theorem convolve_construct (left right : Array Nat)
    (leftPositive : 0 < left.size) (rightPositive : 0 < right.size)
    (leftCanonical : Canonical left) (rightCanonical : Canonical right)
    (admitted : FFT.validSize (left.size + right.size - 1).nextPowerOfTwo = true) :
    ∃ output, FFT.convolve left right = .ok output ∧
      output.size = (left.size + right.size - 1).nextPowerOfTwo ∧
      Canonical output ∧ coeffPolynomial output = coeffPolynomial left * coeffPolynomial right := by
  let n := (left.size + right.size - 1).nextPowerOfTwo
  have coefficientBound : left.size + right.size - 1 ≤ n := nextPower_lower _
  have leftBound : left.size ≤ n := by omega
  have rightBound : right.size ≤ n := by omega
  have nPositive : 0 < n := by omega
  have leftSize := padded_size left n leftBound
  have rightSize := padded_size right n rightBound
  obtain ⟨a, aBuilt, aSize, aCanonical, aValues⟩ :=
    fft_construct (padded left n) (by simpa only [leftSize] using admitted) (padded_canonical left n leftCanonical)
  obtain ⟨b, bBuilt, bSize, bCanonical, bValues⟩ :=
    fft_construct (padded right n) (by simpa only [rightSize] using admitted) (padded_canonical right n rightCanonical)
  have aSize' : a.size = n := aSize.trans leftSize
  have bSize' : b.size = n := bSize.trans rightSize
  let frequencies := (a.zip b).map (fun (x, y) => FFT.mul x y)
  have frequenciesSize : frequencies.size = n := by simp only [frequencies, Array.size_map, Array.size_zip, aSize', bSize', min_self]
  have frequenciesCanonical : Canonical frequencies := by
    intro index bounded
    simp only [frequencies, Array.getElem_map]
    exact Nat.mod_lt _ (by decide)
  obtain ⟨output, outputBuilt, outputSize, outputCanonical, outputValues⟩ :=
    ifft_construct frequencies (by simpa only [frequenciesSize] using admitted) frequenciesCanonical
  let product := coeffPolynomial left * coeffPolynomial right
  have productDegree : product.natDegree < n := by
    have first := finitePolynomial_natDegree left.size (fieldInput left) leftPositive
    have second := finitePolynomial_natDegree right.size (fieldInput right) rightPositive
    have degree : product.natDegree ≤ (coeffPolynomial left).natDegree + (coeffPolynomial right).natDegree :=
      Polynomial.natDegree_mul_le
    change (coeffPolynomial left).natDegree < left.size at first
    change (coeffPolynomial right).natDegree < right.size at second
    omega
  have frequencyValues (index : Nat) (bounded : index < n) :
      fieldInput frequencies index = dft n (domainRoot n) product.coeff index := by
    have ab : index < a.size := by rw [aSize']; exact bounded
    have bb : index < b.size := by rw [bSize']; exact bounded
    have fb : index < frequencies.size := by rw [frequenciesSize]; exact bounded
    have av := aValues index (by rw [leftSize]; exact bounded)
    have bv := bValues index (by rw [rightSize]; exact bounded)
    rw [leftSize] at av
    rw [rightSize] at bv
    have ap' : dft n (domainRoot n) (fieldInput (padded left n)) index =
        (coeffPolynomial left).eval (domainRoot n ^ index) := by
      rw [polynomial_dft (coeffPolynomial left) n _ _ (lt_of_lt_of_le
        (finitePolynomial_natDegree left.size (fieldInput left) leftPositive) leftBound)]
      apply dft_congr
      intro j jb
      rw [coeffPolynomial_coeff, padded_lookup]
    have bp' : dft n (domainRoot n) (fieldInput (padded right n)) index =
        (coeffPolynomial right).eval (domainRoot n ^ index) := by
      rw [polynomial_dft (coeffPolynomial right) n _ _ (lt_of_lt_of_le
        (finitePolynomial_natDegree right.size (fieldInput right) rightPositive) rightBound)]
      apply dft_congr
      intro j jb
      rw [coeffPolynomial_coeff, padded_lookup]
    unfold fieldInput
    rw [getElem!_pos frequencies index fb]
    simp only [frequencies, Array.getElem_map, Array.getElem_zip, model_mul]
    have aValue : model a[index] = dft n (domainRoot n) (fieldInput (padded left n)) index := by
      simpa only [fieldInput, getElem!_pos a index ab] using av
    have bValue : model b[index] = dft n (domainRoot n) (fieldInput (padded right n)) index := by
      simpa only [fieldInput, getElem!_pos b index bb] using bv
    rw [aValue, bValue, ap', bp', ← Polynomial.eval_mul]
    exact polynomial_dft product n _ index productDegree
  refine ⟨output, ?_, outputSize.trans frequenciesSize, outputCanonical, ?_⟩
  · have notEmptyLeft : left.isEmpty = false := by simp [Array.isEmpty, Nat.ne_of_gt leftPositive]
    have notEmptyRight : right.isEmpty = false := by simp [Array.isEmpty, Nat.ne_of_gt rightPositive]
    simp only [FFT.convolve, notEmptyLeft, notEmptyRight, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, admitted, Bool.not_true]
    change (do
      let aa ← FFT.fft (padded left n)
      let bb ← FFT.fft (padded right n)
      if aa.size != bb.size then throw "FFT convolution lengths differ."
      FFT.ifft ((aa.zip bb).map fun (x, y) => FFT.mul x y)) = .ok output
    rw [aBuilt, bBuilt]
    have sameSize : (a.size != b.size) = false := by simp only [aSize', bSize', bne_self_eq_false]
    change (if a.size != b.size then
      (throw "FFT convolution lengths differ." : Except String PUnit) >>= fun _ => FFT.ifft frequencies
      else (pure PUnit.unit : Except String PUnit) >>= fun _ => FFT.ifft frequencies) = .ok output
    rw [sameSize]
    exact outputBuilt
  · apply Polynomial.ext
    intro index
    rw [coeffPolynomial_coeff]
    by_cases bounded : index < n
    · have native := outputValues index (by rw [frequenciesSize]; exact bounded)
      simp only [frequenciesSize] at native
      have transformed : inverseDft n (domainRoot n) (fieldInput frequencies) index =
          inverseDft n (domainRoot n) (dft n (domainRoot n) product.coeff) index := by
        unfold inverseDft
        rw [dft_congr _ _ _ _ frequencyValues]
      rw [transformed, inverseDft_dft n _ _ index nPositive bounded
        (domainRoot_primitive n admitted) (domain_size_nonzero n admitted)] at native
      exact native
    · have outside : ¬index < output.size := by rw [outputSize, frequenciesSize]; exact bounded
      rw [fieldInput, getElem!_neg output index outside]
      have productZero := Polynomial.coeff_eq_zero_of_natDegree_lt (show product.natDegree < index by omega)
      simpa only [model, Nat.cast_zero] using productZero.symm

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.convolve_construct
