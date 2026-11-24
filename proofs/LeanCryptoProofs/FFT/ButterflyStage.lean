import LeanCryptoProofs.FFT.ButterflyBlock
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

def stagePrefix (input : Array Nat) (width half step groups : Nat) : Array Nat :=
  (List.range groups).foldl (fun values group =>
    (blockPrefix values (group * width) half step half).fst) input

theorem stagePrefix_succ (input : Array Nat) (width half step groups : Nat) :
    stagePrefix input width half step (groups + 1) =
      (blockPrefix (stagePrefix input width half step groups) (groups * width) half step half).fst := by
  simp [stagePrefix, List.range_succ, List.foldl_append]

theorem native_butterflyStage (input : Array Nat) (n width root : Nat) :
    FFT.butterflyStage n width root input =
      stagePrefix input width (width / 2) (FFT.powMod root (n / width)) (n / width) := by
  simp [FFT.butterflyStage, stagePrefix, blockPrefix, List.range_eq_range']

def StageInvariant (input : Array Nat) (width half step blocks groups : Nat) (values : Array Nat) : Prop :=
  values.size = input.size ∧ Canonical values ∧
  ∀ block, block < blocks → ∀ index, index < half →
    (model values[block * width + index]! =
      if block < groups then leftButterfly input (block * width) half step index
      else model input[block * width + index]!) ∧
    (model values[block * width + index + half]! =
      if block < groups then rightButterfly input (block * width) half step index
      else model input[block * width + index + half]!)

theorem stagePrefix_invariant (input : Array Nat) (width half step blocks groups : Nat)
    (widthEq : width = half + half) (halfPositive : 0 < half)
    (shape : input.size = blocks * width) (groupsBound : groups ≤ blocks) (canonical : Canonical input) :
    StageInvariant input width half step blocks groups (stagePrefix input width half step groups) := by
  induction groups with
  | zero => simp [stagePrefix, StageInvariant, canonical]
  | succ groups ih =>
    obtain ⟨previousSize, previousCanonical, previousPairs⟩ := ih (by omega)
    have room : groups * width + half + half ≤ (stagePrefix input width half step groups).size := by
      calc
        groups * width + half + half = (groups + 1) * width := by rw [widthEq]; ring
        _ ≤ blocks * width := Nat.mul_le_mul_right width (by omega)
        _ = _ := shape.symm.trans previousSize.symm
    obtain ⟨outputSize, outputPairs, outputOther, outputCanonical⟩ :=
      blockPrefix_complete (stagePrefix input width half step groups) (groups * width) half step room previousCanonical
    rw [stagePrefix_succ]
    refine ⟨outputSize.trans previousSize, outputCanonical, ?_⟩
    intro block blockBound index indexBound
    have blockRoom : block * width + width ≤ input.size := by
      calc
        block * width + width = (block + 1) * width := by ring
        _ ≤ blocks * width := Nat.mul_le_mul_right width (by omega)
        _ = _ := shape.symm
    have leftBound : block * width + index < input.size := by omega
    have rightBound : block * width + index + half < input.size := by omega
    by_cases current : block = groups
    · subst block
      obtain ⟨left, right⟩ := outputPairs index indexBound
      obtain ⟨oldLeft, oldRight⟩ := previousPairs groups (by omega) index indexBound
      simp only [lt_self_iff_false, ↓reduceIte] at oldLeft oldRight
      constructor
      · rw [if_pos (by omega)]
        simpa only [leftButterfly, oldLeft, oldRight] using left
      · rw [if_pos (by omega)]
        simpa only [rightButterfly, oldLeft, oldRight] using right
    · have outsideLeft : block * width + index < groups * width ∨
          groups * width + half + half ≤ block * width + index := by
        by_cases earlier : block < groups
        · left
          have bound : block * width + width ≤ groups * width := by
            simpa only [Nat.add_mul, one_mul] using Nat.mul_le_mul_right width (by omega : block + 1 ≤ groups)
          omega
        · right
          have bound : groups * width + width ≤ block * width := by
            simpa only [Nat.add_mul, one_mul] using Nat.mul_le_mul_right width (by omega : groups + 1 ≤ block)
          omega
      have outsideRight : block * width + index + half < groups * width ∨
          groups * width + half + half ≤ block * width + index + half := by
        by_cases earlier : block < groups
        · left
          have bound : block * width + width ≤ groups * width := by
            simpa only [Nat.add_mul, one_mul] using Nat.mul_le_mul_right width (by omega : block + 1 ≤ groups)
          omega
        · right
          have bound : groups * width + width ≤ block * width := by
            simpa only [Nat.add_mul, one_mul] using Nat.mul_le_mul_right width (by omega : groups + 1 ≤ block)
          omega
      have unchangedLeft := outputOther (block * width + index) (by omega) outsideLeft
      have unchangedRight := outputOther (block * width + index + half) (by omega) outsideRight
      have cut : block < groups + 1 ↔ block < groups := by omega
      constructor
      · rw [unchangedLeft, (previousPairs block blockBound index indexBound).1]
        simp only [cut]
      · rw [unchangedRight, (previousPairs block blockBound index indexBound).2]
        simp only [cut]

theorem stagePrefix_complete (input : Array Nat) (width half step blocks : Nat)
    (widthEq : width = half + half) (halfPositive : 0 < half)
    (shape : input.size = blocks * width) (canonical : Canonical input) :
    (stagePrefix input width half step blocks).size = input.size ∧
    Canonical (stagePrefix input width half step blocks) ∧
    ∀ block, block < blocks → ∀ index, index < half →
      model (stagePrefix input width half step blocks)[block * width + index]! =
        leftButterfly input (block * width) half step index ∧
      model (stagePrefix input width half step blocks)[block * width + index + half]! =
        rightButterfly input (block * width) half step index := by
  obtain ⟨size, bounded, pairs⟩ := stagePrefix_invariant input width half step blocks blocks
    widthEq halfPositive shape (by omega) canonical
  refine ⟨size, bounded, ?_⟩
  intro block blockBound index indexBound
  simpa only [if_pos blockBound] using pairs block blockBound index indexBound

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.stagePrefix_succ
#print axioms LeanCrypto.Proofs.FFT.native_butterflyStage
#print axioms LeanCrypto.Proofs.FFT.stagePrefix_invariant
#print axioms LeanCrypto.Proofs.FFT.stagePrefix_complete
