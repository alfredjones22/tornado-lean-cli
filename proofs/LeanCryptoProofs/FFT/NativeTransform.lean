import LeanCryptoProofs.FFT.TransformInvariant
import LeanCryptoProofs.FFT.DFTInverse
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

theorem canonical_all (input : Array Nat) (canonical : Canonical input) :
    input.all (· < FFT.modulus) = true := by
  simpa only [Array.all_eq_true, decide_eq_true_eq] using canonical

theorem dft_congr (size : Nat) (root : Fr) (left right : Nat → Fr)
    (equal : ∀ index, index < size → left index = right index) (index : Nat) :
    dft size root left index = dft size root right index := by
  unfold dft
  apply Finset.sum_congr rfl
  intro coefficient member
  rw [equal coefficient (Finset.mem_range.mp member)]

/-- Construction theorem for the actual forward transform, for every
canonical input of every admitted radix-two size. -/
theorem fft_construct (input : Array Nat) (admitted : FFT.validSize input.size = true)
    (canonical : Canonical input) :
    ∃ output, FFT.fft input = .ok output ∧ output.size = input.size ∧ Canonical output ∧
      ∀ index, index < input.size →
        fieldInput output index = dft input.size (domainRoot input.size) (fieldInput input) index := by
  let root := constructedRoot input.size
  let bits := Nat.log2 input.size
  have shape : input.size = 2 ^ bits := (admitted_log_bound input.size admitted).2.symm
  have primitive : IsPrimitiveRoot (model root) (2 ^ bits) := by
    rw [← shape]
    exact domainRoot_primitive input.size admitted
  obtain ⟨size, bounded, values⟩ := computedStages_dft input root bits shape canonical primitive
  refine ⟨computedStages input root bits bits, ?_, size, bounded, values⟩
  change nativeTransform input false = _
  rw [nativeTransform_eq_decomposed]
  simp only [transformDecomposed, (rootOfUnity_constructed input.size admitted).1,
    canonical_all input canonical, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem inverse_selected_root (size : Nat) (root : Fr) (positive : 0 < size)
    (primitive : IsPrimitiveRoot root size) : root ^ (size - 1) = root⁻¹ := by
  have nonzero := (primitive.isUnit (Nat.ne_of_gt positive)).ne_zero
  apply mul_left_cancel₀ nonzero
  rw [mul_inv_cancel₀ nonzero, ← pow_succ']
  rw [Nat.sub_add_cancel positive, primitive.pow_eq_one]

/-- The actual inverse transform constructs the independently defined inverse
DFT. Its size inverse is proved by Fermat, rather than assumed accepted. -/
theorem ifft_construct (input : Array Nat) (admitted : FFT.validSize input.size = true)
    (canonical : Canonical input) :
    ∃ output, FFT.ifft input = .ok output ∧ output.size = input.size ∧ Canonical output ∧
      ∀ index, index < input.size →
        fieldInput output index = inverseDft input.size (domainRoot input.size) (fieldInput input) index := by
  let root := constructedRoot input.size
  let selected := FFT.powMod root (input.size - 1)
  let bits := Nat.log2 input.size
  let scale := ((model input.size)⁻¹).val
  have shape : input.size = 2 ^ bits := (admitted_log_bound input.size admitted).2.symm
  have positive : 0 < input.size := by
    rw [shape]
    exact pow_pos (by decide) _
  have rootInverse : model selected = (domainRoot input.size)⁻¹ := by
    dsimp [selected]
    rw [model_powMod]
    exact inverse_selected_root input.size _ positive (domainRoot_primitive input.size admitted)
  have primitive : IsPrimitiveRoot (model selected) (2 ^ bits) := by
    rw [rootInverse, ← shape]
    exact (domainRoot_primitive input.size admitted).inv
  obtain ⟨size, bounded, values⟩ := computedStages_dft input selected bits shape canonical primitive
  let stages := computedStages input selected bits bits
  let output := stages.map (fun value => FFT.mul value scale)
  have inverse : FFT.inverse input.size = .ok scale :=
    inverse_complete input.size (domain_size_nonzero input.size admitted)
  refine ⟨output, ?_, ?_, ?_, ?_⟩
  · change nativeTransform input true = _
    rw [nativeTransform_eq_decomposed]
    simp only [transformDecomposed, (rootOfUnity_constructed input.size admitted).1,
      canonical_all input canonical, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    change sourceCore input root true = .ok output
    simp only [sourceCore, ↓reduceIte, inverse]
    rfl
  · simpa only [output, Array.size_map] using size
  · intro index indexBound
    have originalBound : index < stages.size := by simpa only [output, Array.size_map] using indexBound
    simp only [output, Array.getElem_map]
    exact Nat.mod_lt _ (by decide)
  · intro index indexBound
    have stageBound : index < stages.size := by rw [size]; exact indexBound
    change model output[index]! = _
    simp only [output, getElem!_pos (stages.map (fun value => FFT.mul value scale)) index
      (by simpa only [Array.size_map] using stageBound),
      Array.getElem_map, model_mul]
    have stageValue : model stages[index] = dft input.size (model selected) (fieldInput input) index := by
      simpa only [getElem!_pos (computedStages input selected bits bits) index stageBound] using values index indexBound
    rw [stageValue, rootInverse, model_val]
    exact mul_comm _ _

theorem fft_ifft_roundtrip (input : Array Nat) (admitted : FFT.validSize input.size = true)
    (canonical : Canonical input) :
    ∃ transformed, FFT.fft input = .ok transformed ∧ FFT.ifft transformed = .ok input := by
  obtain ⟨transformed, forward, transformedSize, transformedCanonical, forwardValues⟩ :=
    fft_construct input admitted canonical
  obtain ⟨result, backward, resultSize, resultCanonical, backwardValues⟩ :=
    ifft_construct transformed (by simpa only [transformedSize] using admitted) transformedCanonical
  refine ⟨transformed, forward, ?_⟩
  have equal : result = input := by
    apply Array.ext (resultSize.trans transformedSize)
    intro index resultBound inputBound
    apply canonical_injective (resultCanonical index resultBound) (canonical index inputBound)
    have value := backwardValues index (by simpa only [transformedSize] using inputBound)
    simp only [transformedSize] at value
    have sourceEqual : inverseDft input.size (domainRoot input.size) (fieldInput transformed) index =
        inverseDft input.size (domainRoot input.size)
          (dft input.size (domainRoot input.size) (fieldInput input)) index := by
      unfold inverseDft
      rw [dft_congr _ _ _ _ forwardValues]
    rw [sourceEqual, inverseDft_dft input.size _ _ index
      (by have s := (admitted_log_bound input.size admitted).2; rw [← s]; exact pow_pos (by decide) _)
      inputBound (domainRoot_primitive input.size admitted) (domain_size_nonzero input.size admitted)] at value
    simpa only [fieldInput, getElem!_pos result index resultBound,
      getElem!_pos input index inputBound] using value
  rw [equal] at backward
  exact backward

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.canonical_all
#print axioms LeanCrypto.Proofs.FFT.dft_congr
#print axioms LeanCrypto.Proofs.FFT.fft_construct
#print axioms LeanCrypto.Proofs.FFT.inverse_selected_root
#print axioms LeanCrypto.Proofs.FFT.ifft_construct
#print axioms LeanCrypto.Proofs.FFT.fft_ifft_roundtrip
