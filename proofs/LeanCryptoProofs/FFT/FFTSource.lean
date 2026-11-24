import LeanCryptoProofs.FFT.BitPermutation
import LeanCryptoProofs.FrModel
import Lean
open Lean Elab Term Meta
elab "actualFFTTransform" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Groth16.FFT `LeanCrypto.Groth16.FFT.transform)

set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16

abbrev nativeTransform (input : Array Nat) (inverse : Bool) : Except String (Array Nat) :=
  actualFFTTransform input inverse

def sourceReverse {A : Type} [Inhabited A] (input : Array A) (bits : Nat) : Array A := Id.run do
  let mut values := input
  for i in [0:input.size] do
    let j := FFT.reverseBits i bits
    if i < j then
      let left := values[i]!
      values := values.set! i values[j]!
      values := values.set! j left
  return values

def sourceStages (values : Array Nat) (n bits selectedRoot : Nat) : Array Nat := Id.run do
  let mut result := values
  for stage in [0:bits] do
    result := FFT.butterflyStage n (2 ^ (stage + 1)) selectedRoot result
  return result

theorem sourceReverse_eq_prefix {A : Type} [Inhabited A] (input : Array A) (bits : Nat) :
    sourceReverse input bits = reversePrefix input bits input.size := by
  simp [sourceReverse, reversePrefix, native_reverseBits, swapSource, List.range_eq_range']
  have move (condition : Prop) [Decidable condition] (yes no : Array A) :
      (if condition then (pure (ForInStep.yield yes) : Id (ForInStep (Array A)))
        else pure (ForInStep.yield no)) =
      pure (ForInStep.yield (if condition then yes else no)) := by split <;> rfl
  simp_rw [move]
  simp

theorem sourceStages_eq_fold (values : Array Nat) (n bits root : Nat) :
    sourceStages values n bits root =
      (List.range bits).foldl (fun result stage => FFT.butterflyStage n (2 ^ (stage + 1)) root result) values := by
  simp [sourceStages, List.range_eq_range']

theorem sourceReverse_permutation {A : Type} [Inhabited A]
    (input : Array A) (bits : Nat) (shape : input.size = 2 ^ bits) :
    (sourceReverse input bits).size = input.size ∧
      ∀ index, index < input.size → (sourceReverse input bits)[index]! = input[reverseNat bits index]! := by
  rw [sourceReverse_eq_prefix]
  exact reversePrefix_permutation input bits shape

def nativeBody (input : Array Nat) (inverseDirection : Bool) :
    Except String (Array Nat) := do
  let n := input.size
  let root ← FFT.rootOfUnity n
  if !input.all (· < FFT.modulus) then throw "FFT input is outside BN254 Fr."
  let selectedRoot := if inverseDirection then FFT.powMod root (n - 1) else root
  let bits := Nat.log2 n
  let mut values := input
  for i in [0:n] do
    let j := FFT.reverseBits i bits
    if i < j then
      let left := values[i]!
      values := values.set! i values[j]!
      values := values.set! j left
  for stage in [0:bits] do
    values := FFT.butterflyStage n (2 ^ (stage + 1)) selectedRoot values
  if inverseDirection then
    let nInverse ← FFT.inverse n
    values := values.map (fun value => FFT.mul value nInverse)
  return values


theorem nativeTransform_definition (input : Array Nat) (direction : Bool) :
    nativeTransform input direction = nativeBody input direction := rfl

def sourceCore (input : Array Nat) (root : Nat) (direction : Bool) : Except String (Array Nat) := do
  let n := input.size
  let selected := if direction then FFT.powMod root (n - 1) else root
  let values := sourceStages (sourceReverse input (Nat.log2 n)) n (Nat.log2 n) selected
  if direction then
    let scale ← FFT.inverse n
    return values.map (fun value => FFT.mul value scale)
  else return values

def transformDecomposed (input : Array Nat) (direction : Bool) : Except String (Array Nat) := do
  let root ← FFT.rootOfUnity input.size
  if !input.all (· < FFT.modulus) then throw "FFT input is outside BN254 Fr."
  sourceCore input root direction

theorem nativeTransform_eq_decomposed (input : Array Nat) (direction : Bool) :
    nativeTransform input direction = transformDecomposed input direction := by
  rw [nativeTransform_definition]
  simp [nativeBody, transformDecomposed, sourceCore, sourceReverse, sourceStages]
  have moveExcept (condition : Prop) [Decidable condition] (yes no : Array Nat) :
      (if condition then (pure (ForInStep.yield yes) : Except String (ForInStep (Array Nat)))
        else pure (ForInStep.yield no)) =
      pure (ForInStep.yield (if condition then yes else no)) := by split <;> rfl
  have moveId (condition : Prop) [Decidable condition] (yes no : Array Nat) :
      (if condition then (pure (ForInStep.yield yes) : Id (ForInStep (Array Nat)))
        else pure (ForInStep.yield no)) =
      pure (ForInStep.yield (if condition then yes else no)) := by split <;> rfl
  simp_rw [moveExcept, moveId]
  simp


def computedStages (input : Array Nat) (root total length : Nat) : Array Nat :=
  sourceStages (sourceReverse input total) input.size length root

theorem computedStages_zero (input : Array Nat) (root total : Nat) :
    computedStages input root total 0 = sourceReverse input total := by
  simp [computedStages, sourceStages]

theorem computedStages_succ (input : Array Nat) (root total length : Nat) :
    computedStages input root total (length + 1) =
      FFT.butterflyStage input.size (2 ^ (length + 1)) root (computedStages input root total length) := by
  simp [computedStages, sourceStages_eq_fold, List.range_succ, List.foldl_append]

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.sourceReverse_eq_prefix
#print axioms LeanCrypto.Proofs.FFT.sourceStages_eq_fold
#print axioms LeanCrypto.Proofs.FFT.sourceReverse_permutation

#print axioms LeanCrypto.Proofs.FFT.nativeTransform_definition
#print axioms LeanCrypto.Proofs.FFT.nativeTransform_eq_decomposed

#print axioms LeanCrypto.Proofs.FFT.computedStages_zero
#print axioms LeanCrypto.Proofs.FFT.computedStages_succ
