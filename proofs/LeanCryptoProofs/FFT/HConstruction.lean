import LeanCryptoProofs.FFT.Convolution
import LeanCryptoProofs.FFT.InversePolynomial
import LeanCryptoProofs.FFT.SparseModel
import LeanCryptoProofs.FFT.TrimModel
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

theorem proving_convolution_size (domain : Nat) (admitted : FFT.validSize domain = true)
    (minimum : 2 ≤ domain) :
    (domain + domain - 1).nextPowerOfTwo = domain + domain := by
  have shape := (admitted_log_bound domain admitted).2
  have target : domain + domain = 2 ^ (Nat.log2 domain + 1) := by rw [pow_succ, shape]; omega
  rw [target]
  apply nextPower_exact
  · rw [pow_succ, shape, Nat.mul_div_cancel _ (by decide)]
    omega
  · omega

theorem proving_convolution_admitted (domain : Nat) (admitted : FFT.validSize domain = true)
    (bounded : domain ≤ FFT.provingDomainSize) :
    FFT.validSize (domain + domain) = true := by
  have shape := (admitted_log_bound domain admitted).2
  have positive : 0 < domain := by rw [← shape]; exact pow_pos (by decide) _
  have doubled : domain + domain = 2 ^ (Nat.log2 domain + 1) := by rw [pow_succ, shape]; omega
  have maximum : domain + domain ≤ FFT.maximumSize := by
    change domain ≤ 32768 at bounded
    change domain + domain ≤ 65536
    omega
  simp only [FFT.validSize, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨by omega, maximum⟩, ?_⟩
  rw [doubled, Nat.log2_two_pow]

def ValidSparseInput (domain : Nat) (witness : Array Nat) (polynomials : Array Types.Polynomial) : Prop :=
  witness.size = polynomials.size ∧
    ∀ signal, signal < witness.size → ValidEntries domain polynomials[signal]!.entries.toList

/-- Complete source construction through sparse accumulation, inverse FFT,
ordinary convolution, high-half extraction, and trailing-zero trimming. -/
theorem calculateH_construct_strict (domain : Nat) (witness : Array Nat)
    (polsA polsB : Array Types.Polynomial)
    (admitted : FFT.validSize domain = true) (domainBound : domain ≤ FFT.provingDomainSize)
    (minimum : 2 ≤ domain) (positive : 0 < witness.size) (canonical : Canonical witness)
    (validA : ValidSparseInput domain witness polsA) (validB : ValidSparseInput domain witness polsB) :
    ∃ a b h, FFT.calculateH domain witness polsA polsB = .ok h ∧
      FFT.ifft (sourceEvaluations domain witness polsA) = .ok a ∧
      FFT.ifft (sourceEvaluations domain witness polsB) = .ok b ∧
      a.size = domain ∧ b.size = domain ∧ h.size ≤ domain - 1 ∧ Canonical h ∧
      coeffPolynomial h = highHalf domain (coeffPolynomial a * coeffPolynomial b) ∧
      (∀ row, row < domain → (coeffPolynomial a).eval (domainRoot domain ^ row) = sparseRow witness polsA row) ∧
      (∀ row, row < domain → (coeffPolynomial b).eval (domainRoot domain ^ row) = sparseRow witness polsB row) := by
  obtain ⟨pA, pABuilt, pASize, pACanonical, pAValues⟩ :=
    sumEvaluations_construct domain witness polsA admitted domainBound validA.1 positive canonical validA.2
  obtain ⟨pB, pBBuilt, pBSize, pBCanonical, pBValues⟩ :=
    sumEvaluations_construct domain witness polsB admitted domainBound validB.1 positive canonical validB.2
  obtain ⟨a, aBuilt, aSize, aCanonical, aValues⟩ :=
    ifft_polynomial_construct pA (by simpa only [pASize] using admitted) pACanonical
  obtain ⟨b, bBuilt, bSize, bCanonical, bValues⟩ :=
    ifft_polynomial_construct pB (by simpa only [pBSize] using admitted) pBCanonical
  have aSize' : a.size = domain := aSize.trans pASize
  have bSize' : b.size = domain := bSize.trans pBSize
  have convolutionSize : (a.size + b.size - 1).nextPowerOfTwo = domain + domain := by
    rw [aSize', bSize']
    exact proving_convolution_size domain admitted minimum
  obtain ⟨product, productBuilt, productSize, productCanonical, productPolynomial⟩ :=
    convolve_construct a b (by omega) (by omega) aCanonical bCanonical
      (by rw [convolutionSize]; exact proving_convolution_admitted domain admitted domainBound)
  have productSize' : product.size = domain + domain := productSize.trans convolutionSize
  let high := product.extract domain product.size
  let h := nativeTrim high
  have highCanonical := extract_canonical product domain product.size productCanonical
  obtain ⟨hSize, hCanonical, hPolynomial⟩ := nativeTrim_preserves high highCanonical
  have highSize : high.size = domain := by simp only [high, Array.size_extract, min_self, productSize']; omega
  have productDegree : (coeffPolynomial product).natDegree < domain + domain - 1 := by
    rw [productPolynomial]
    have aDegree : (coeffPolynomial a).natDegree < domain := by
      have degree : (coeffPolynomial a).natDegree < a.size :=
        finitePolynomial_natDegree a.size (fieldInput a) (by omega)
      simpa only [aSize'] using degree
    have bDegree : (coeffPolynomial b).natDegree < domain := by
      have degree : (coeffPolynomial b).natDegree < b.size :=
        finitePolynomial_natDegree b.size (fieldInput b) (by omega)
      simpa only [bSize'] using degree
    exact lt_of_le_of_lt Polynomial.natDegree_mul_le
      (show (coeffPolynomial a).natDegree + (coeffPolynomial b).natDegree < domain + domain - 1 by omega)
  have highLastModel : fieldInput high (domain - 1) = 0 := by
    rw [← coeffPolynomial_coeff, extract_highHalf product domain productSize', highHalf,
      finitePolynomial_coeff, if_pos (show domain - 1 < domain by omega)]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have address : domain + (domain - 1) = domain + domain - 1 := by omega
    rw [address]
    exact productDegree
  have highLastZero : high[high.size - 1]! = 0 := by
    have lastBound : high.size - 1 < high.size := by omega
    have canonicalLast : high[high.size - 1]! < Q := by
      rw [getElem!_pos high (high.size - 1) lastBound]
      exact highCanonical _ lastBound
    apply canonical_injective canonicalLast (by decide)
    simpa only [fieldInput, highSize] using highLastModel
  have strictSize : h.size ≤ domain - 1 := by
    have bound := nativeTrim_zero_tail_size high highCanonical (by omega) highLastZero
    simpa only [highSize] using bound
  have pASource : pA = sourceEvaluations domain witness polsA := by
    have source := sumEvaluations_source domain witness polsA admitted domainBound validA.1 positive canonical validA.2
    rw [pABuilt] at source
    exact Except.ok.inj source
  have pBSource : pB = sourceEvaluations domain witness polsB := by
    have source := sumEvaluations_source domain witness polsB admitted domainBound validB.1 positive canonical validB.2
    rw [pBBuilt] at source
    exact Except.ok.inj source
  refine ⟨a, b, h, ?_, ?_, ?_, aSize', bSize', strictSize, hCanonical, ?_, ?_, ?_⟩
  · rw [FFT.calculateH]
    simp only [if_neg (show ¬domain < 2 by omega)]
    rw [pABuilt, pBBuilt]
    change (do
      let aa ← FFT.ifft pA
      let bb ← FFT.ifft pB
      let pp ← FFT.convolve aa bb
      if pp.size != 2 * domain then throw "Unexpected H polynomial convolution size."
      return nativeTrim (pp.extract domain pp.size)) = .ok h
    rw [aBuilt, bBuilt]
    change (do
      let pp ← FFT.convolve a b
      if pp.size != 2 * domain then throw "Unexpected H polynomial convolution size."
      return nativeTrim (pp.extract domain pp.size)) = .ok h
    rw [productBuilt]
    change (if product.size != 2 * domain then
      (throw "Unexpected H polynomial convolution size." : Except String PUnit) >>= fun _ => pure h
      else (pure PUnit.unit : Except String PUnit) >>= fun _ => pure h) = .ok h
    have same : (product.size != 2 * domain) = false := by rw [productSize']; simp only [two_mul, bne_self_eq_false]
    rw [same]
    rfl
  · simpa only [← pASource] using aBuilt
  · simpa only [← pBSource] using bBuilt
  · rw [hPolynomial, extract_highHalf product domain productSize', productPolynomial]
  · intro row rowBound
    have values := aValues row (by rw [pASize]; exact rowBound)
    rw [pASize, pAValues row rowBound] at values
    exact values
  · intro row rowBound
    have values := bValues row (by rw [pBSize]; exact rowBound)
    rw [pBSize, pBValues row rowBound] at values
    exact values

theorem calculateH_construct (domain : Nat) (witness : Array Nat)
    (polsA polsB : Array Types.Polynomial)
    (admitted : FFT.validSize domain = true) (domainBound : domain ≤ FFT.provingDomainSize)
    (minimum : 2 ≤ domain) (positive : 0 < witness.size) (canonical : Canonical witness)
    (validA : ValidSparseInput domain witness polsA) (validB : ValidSparseInput domain witness polsB) :
    ∃ a b h, FFT.calculateH domain witness polsA polsB = .ok h ∧
      FFT.ifft (sourceEvaluations domain witness polsA) = .ok a ∧
      FFT.ifft (sourceEvaluations domain witness polsB) = .ok b ∧
      a.size = domain ∧ b.size = domain ∧ h.size ≤ domain ∧ Canonical h ∧
      coeffPolynomial h = highHalf domain (coeffPolynomial a * coeffPolynomial b) ∧
      (∀ row, row < domain → (coeffPolynomial a).eval (domainRoot domain ^ row) = sparseRow witness polsA row) ∧
      (∀ row, row < domain → (coeffPolynomial b).eval (domainRoot domain ^ row) = sparseRow witness polsB row) := by
  obtain ⟨a, b, h, built, aBuilt, bBuilt, aSize, bSize, strict, bounded, high, aRows, bRows⟩ :=
    calculateH_construct_strict domain witness polsA polsB admitted domainBound minimum positive canonical validA validB
  exact ⟨a, b, h, built, aBuilt, bBuilt, aSize, bSize, by omega, bounded, high, aRows, bRows⟩

/-- Actual H output fits the domain-minus-one setup query. This follows
from product degree at most 2m−2 and the actual first trimming pop. -/
theorem calculateH_success_dimension (domain : Nat) (witness : Array Nat)
    (polsA polsB : Array Types.Polynomial)
    (admitted : FFT.validSize domain = true) (domainBound : domain ≤ FFT.provingDomainSize)
    (minimum : 2 ≤ domain) (positive : 0 < witness.size) (canonical : Canonical witness)
    (validA : ValidSparseInput domain witness polsA) (validB : ValidSparseInput domain witness polsB)
    (h : Array Nat) (returned : FFT.calculateH domain witness polsA polsB = .ok h) : h.size ≤ domain - 1 := by
  obtain ⟨_, _, constructed, built, _, _, _, _, size, _⟩ :=
    calculateH_construct_strict domain witness polsA polsB admitted domainBound minimum positive canonical validA validB
  have equal : constructed = h := Except.ok.inj (built.symm.trans returned)
  simpa only [equal] using size

/-- Source-level QAP quotient construction against independently supplied
degree-bounded A/B/C polynomials and their original sparse-row alignment.
Neither a quotient equation nor a final verifier result is a premise. -/
theorem calculateH_quotient (domain : Nat) (witness : Array Nat)
    (polsA polsB : Array Types.Polynomial)
    (admitted : FFT.validSize domain = true) (domainBound : domain ≤ FFT.provingDomainSize)
    (minimum : 2 ≤ domain) (positive : 0 < witness.size) (canonical : Canonical witness)
    (validA : ValidSparseInput domain witness polsA) (validB : ValidSparseInput domain witness polsB)
    (a b c : Polynomial Fr) (aDegree : a.natDegree < domain)
    (bDegree : b.natDegree < domain) (cDegree : c.natDegree < domain)
    (aAlignment : ∀ row, row < domain → a.eval (domainRoot domain ^ row) = sparseRow witness polsA row)
    (bAlignment : ∀ row, row < domain → b.eval (domainRoot domain ^ row) = sparseRow witness polsB row)
    (rows : ∀ row, row < domain →
      sparseRow witness polsA row * sparseRow witness polsB row = c.eval (domainRoot domain ^ row)) :
    ∃ h, FFT.calculateH domain witness polsA polsB = .ok h ∧ Canonical h ∧ h.size ≤ domain ∧
      coeffPolynomial h * (Polynomial.X ^ domain - 1) = a * b - c := by
  obtain ⟨actualA, actualB, h, built, _, _, aSize, bSize, hSize, hCanonical, high, aRows, bRows⟩ :=
    calculateH_construct domain witness polsA polsB admitted domainBound minimum positive canonical validA validB
  have domainPositive : 0 < domain := by omega
  have actualADegree : (coeffPolynomial actualA).natDegree < domain := by
    have degree : (coeffPolynomial actualA).natDegree < actualA.size :=
      finitePolynomial_natDegree actualA.size (fieldInput actualA) (by omega)
    simpa only [aSize] using degree
  have actualBDegree : (coeffPolynomial actualB).natDegree < domain := by
    have degree : (coeffPolynomial actualB).natDegree < actualB.size :=
      finitePolynomial_natDegree actualB.size (fieldInput actualB) (by omega)
    simpa only [bSize] using degree
  have equalsA : coeffPolynomial actualA = a := polynomial_eq_of_domain_eval domain (domainRoot domain)
    (domainRoot_primitive domain admitted) domainPositive (domain_size_nonzero domain admitted)
    _ _ actualADegree aDegree (fun row bound => (aRows row bound).trans (aAlignment row bound).symm)
  have equalsB : coeffPolynomial actualB = b := polynomial_eq_of_domain_eval domain (domainRoot domain)
    (domainRoot_primitive domain admitted) domainPositive (domain_size_nonzero domain admitted)
    _ _ actualBDegree bDegree (fun row bound => (bRows row bound).trans (bAlignment row bound).symm)
  rw [equalsA, equalsB] at high
  refine ⟨h, built, hCanonical, hSize, ?_⟩
  rw [high]
  symm
  have productDegree : (a * b).natDegree < domain + domain :=
    lt_of_le_of_lt Polynomial.natDegree_mul_le (show a.natDegree + b.natDegree < domain + domain by omega)
  apply highHalf_quotient domain (domainRoot domain) (domainRoot_primitive domain admitted)
    domainPositive (domain_size_nonzero domain admitted) (a * b) c productDegree cDegree
  intro row bounded
  rw [Polynomial.eval_mul, aAlignment row bounded, bAlignment row bounded]
  exact rows row bounded

/-- Any actual returned coefficient array carries the quotient equation,
including its scalar evaluation at every setup point. -/
theorem calculateH_success_quotient (domain : Nat) (witness : Array Nat)
    (polsA polsB : Array Types.Polynomial)
    (admitted : FFT.validSize domain = true) (domainBound : domain ≤ FFT.provingDomainSize)
    (minimum : 2 ≤ domain) (positive : 0 < witness.size) (canonical : Canonical witness)
    (validA : ValidSparseInput domain witness polsA) (validB : ValidSparseInput domain witness polsB)
    (a b c : Polynomial Fr) (aDegree : a.natDegree < domain)
    (bDegree : b.natDegree < domain) (cDegree : c.natDegree < domain)
    (aAlignment : ∀ row, row < domain → a.eval (domainRoot domain ^ row) = sparseRow witness polsA row)
    (bAlignment : ∀ row, row < domain → b.eval (domainRoot domain ^ row) = sparseRow witness polsB row)
    (rows : ∀ row, row < domain →
      sparseRow witness polsA row * sparseRow witness polsB row = c.eval (domainRoot domain ^ row))
    (h : Array Nat) (returned : FFT.calculateH domain witness polsA polsB = .ok h) :
    Canonical h ∧ h.size ≤ domain ∧
      coeffPolynomial h * (Polynomial.X ^ domain - 1) = a * b - c ∧
      ∀ tau : Fr, a.eval tau * b.eval tau - c.eval tau =
        (coeffPolynomial h).eval tau * (tau ^ domain - 1) := by
  obtain ⟨constructed, built, bounded, size, equation⟩ :=
    calculateH_quotient domain witness polsA polsB admitted domainBound minimum positive canonical
      validA validB a b c aDegree bDegree cDegree aAlignment bAlignment rows
  have equal : constructed = h := Except.ok.inj (built.symm.trans returned)
  subst constructed
  refine ⟨bounded, size, equation, ?_⟩
  intro tau
  have evaluated := congrArg (fun polynomial : Polynomial Fr => polynomial.eval tau) equation
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one] using evaluated.symm

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.proving_convolution_size
#print axioms LeanCrypto.Proofs.FFT.proving_convolution_admitted
#print axioms LeanCrypto.Proofs.FFT.calculateH_construct_strict
#print axioms LeanCrypto.Proofs.FFT.calculateH_construct
#print axioms LeanCrypto.Proofs.FFT.calculateH_success_dimension
#print axioms LeanCrypto.Proofs.FFT.calculateH_quotient
#print axioms LeanCrypto.Proofs.FFT.calculateH_success_quotient
