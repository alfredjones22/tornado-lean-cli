import LeanCryptoProofs.FFT.ButterflyStage
import LeanCryptoProofs.FFT.DFTButterfly
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

def fieldInput (input : Array Nat) (index : Nat) : Fr := model input[index]!

def TransformInvariant (input : Array Nat) (root total stage : Nat) (values : Array Nat) : Prop :=
  values.size = input.size ∧ Canonical values ∧
  ∀ group, group < 2 ^ (total - stage) → ∀ index, index < 2 ^ stage →
    model values[group * 2 ^ stage + index]! =
      stageValue (fieldInput input) (model root) total stage group index

theorem computedStages_invariant (input : Array Nat) (root total length : Nat)
    (shape : input.size = 2 ^ total) (canonical : Canonical input)
    (primitive : IsPrimitiveRoot (model root) (2 ^ total)) (lengthBound : length ≤ total) :
    TransformInvariant input root total length (computedStages input root total length) := by
  induction length with
  | zero =>
    rw [computedStages_zero]
    obtain ⟨sameSize, permutation⟩ := sourceReverse_permutation input total shape
    refine ⟨sameSize, ?_, ?_⟩
    · intro index indexBound
      have originalBound : reverseNat total index < input.size := by rw [shape]; exact reverseNat_bound _ _
      have indexOriginal : index < input.size := by simpa only [sameSize] using indexBound
      have value : (sourceReverse input total)[index]! < Q := by
        rw [permutation index indexOriginal]
        simpa [originalBound] using canonical (reverseNat total index) originalBound
      simpa [indexBound] using value
    · intro group groupBound index indexBound
      have indexZero : index = 0 := by simpa using indexBound
      subst index
      simp only [pow_zero, mul_one, add_zero, stageValue_initial]
      exact congrArg model (permutation group (by simpa only [shape] using groupBound))
  | succ length ih =>
    have within : length < total := by omega
    obtain ⟨previousSize, previousCanonical, previousValues⟩ := ih (by omega)
    let half := 2 ^ length
    let width := 2 ^ (length + 1)
    let groups := 2 ^ (total - (length + 1))
    let step := FFT.powMod root groups
    have widthEq : width = half + half := by dsimp [width, half]; rw [pow_succ]; omega
    have halfPositive : 0 < half := pow_pos (by decide) _
    have widthPositive : 0 < width := by omega
    have halfEq : width / 2 = half := by
      dsimp [width, half]
      rw [pow_succ]
      exact Nat.mul_div_cancel _ (by decide)
    have groupShape : input.size = groups * width := by
      rw [shape]
      dsimp [groups, width]
      rw [← pow_add]
      congr 1
      omega
    have groupCount : input.size / width = groups := by
      rw [groupShape]
      exact Nat.mul_div_cancel _ widthPositive
    have oldGroupCount : 2 ^ (total - length) = 2 * groups := by
      have difference : total - length = total - (length + 1) + 1 := by omega
      rw [difference, pow_succ']
    obtain ⟨outputSize, outputCanonical, pairs⟩ := stagePrefix_complete
      (computedStages input root total length) width half step groups
      widthEq halfPositive (previousSize.trans groupShape) previousCanonical
    rw [computedStages_succ, native_butterflyStage]
    change TransformInvariant input root total (length + 1)
      (stagePrefix (computedStages input root total length) width (width / 2)
        (FFT.powMod root (input.size / width)) (input.size / width))
    rw [halfEq, groupCount]
    refine ⟨outputSize.trans previousSize, outputCanonical, ?_⟩
    intro group groupBound index indexBound
    have groupBound' : group < groups := groupBound
    have leftGroup : 2 * group < 2 ^ (total - length) := by rw [oldGroupCount]; omega
    have rightGroup : 2 * group + 1 < 2 ^ (total - length) := by rw [oldGroupCount]; omega
    have twiddle (j : Nat) : model step ^ j = model root ^ (j * groups) := by
      dsimp [step]
      rw [model_powMod, ← pow_mul, Nat.mul_comm groups j]
    have oldLeft (j : Nat) (bounded : j < half) :
        model (computedStages input root total length)[group * width + j]! =
          stageValue (fieldInput input) (model root) total length (2 * group) j := by
      have address : group * width + j = (2 * group) * 2 ^ length + j := by
        dsimp [width]
        rw [pow_succ]
        ring
      rw [address]
      exact previousValues (2 * group) leftGroup j bounded
    have oldRight (j : Nat) (bounded : j < half) :
        model (computedStages input root total length)[group * width + j + half]! =
          stageValue (fieldInput input) (model root) total length (2 * group + 1) j := by
      have address : group * width + j + half = (2 * group + 1) * 2 ^ length + j := by
        dsimp [width, half]
        rw [pow_succ]
        ring
      rw [address]
      exact previousValues (2 * group + 1) rightGroup j bounded
    by_cases lower : index < half
    · rw [(pairs group groupBound' index lower).1]
      unfold leftButterfly
      rw [oldLeft index lower, oldRight index lower, twiddle]
      exact (stageValue_left (fieldInput input) (model root) total length group index within).symm
    · let j := index - half
      have jBound : j < half := by omega
      have indexEq : j + half = index := by omega
      have address : group * 2 ^ (length + 1) + index = group * width + j + half := by
        dsimp [width]
        omega
      rw [address, (pairs group groupBound' j jBound).2]
      unfold rightButterfly
      rw [oldLeft j jBound, oldRight j jBound, twiddle]
      have totalPositive : 0 < total := by omega
      have totalSucc : total - 1 + 1 = total := by omega
      have halfRoot : model root ^ (2 ^ (total - 1)) = -1 :=
        primitive_half_neg_one (model root) (total - 1) (by rw [totalSucc]; exact primitive)
      have upper := stageValue_upper (fieldInput input) (model root) total length group j within halfRoot
      rw [indexEq] at upper
      exact upper.symm

/-- Arbitrary radix-two length: the actual complete butterfly stage sequence
computes the independent DFT, after the actual bit-reversal swap pass. -/
theorem computedStages_dft (input : Array Nat) (root total : Nat)
    (shape : input.size = 2 ^ total) (canonical : Canonical input)
    (primitive : IsPrimitiveRoot (model root) (2 ^ total)) :
    (computedStages input root total total).size = input.size ∧
    Canonical (computedStages input root total total) ∧
    ∀ index, index < input.size →
      model (computedStages input root total total)[index]! = dft input.size (model root) (fieldInput input) index := by
  obtain ⟨sameSize, bounded, values⟩ := computedStages_invariant input root total total shape canonical primitive (by omega)
  refine ⟨sameSize, bounded, ?_⟩
  intro index indexBound
  have result := values 0 (by simp) index (by simpa only [shape] using indexBound)
  simpa only [zero_mul, zero_add, stageValue_final, shape] using result

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.computedStages_invariant
#print axioms LeanCrypto.Proofs.FFT.computedStages_dft
