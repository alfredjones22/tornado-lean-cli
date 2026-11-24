import LeanCrypto.Groth16.Verify
import LeanCryptoProofs.AssemblyQap

open Lean Elab Term Meta
elab "actualVerifierInputCandidate" : term =>
  mkConstWithFreshMVarLevels
    (mkPrivateNameCore `LeanCrypto.Groth16.Verify `LeanCrypto.Groth16.Verify.publicInputPointCandidate)

set_option autoImplicit false
namespace LeanCrypto.Proofs.NativeVerifier
open LeanCrypto.BN254.G1 LeanCrypto.Groth16.Verify

abbrev nativeInputCandidate (key : VerifyingKey) (signals : Array Nat) : Except String Affine :=
  actualVerifierInputCandidate key signals

def inputStep (key : VerifyingKey) (signals : Array Nat) (state : Jacobian) (index : Nat) : Except String Jacobian := do
  let some point := key.ic[index+1]?
    | throw "Groth16 verification key is missing an IC point."
  return state.add ((Jacobian.ofAffine point).scalarMul signals[index]!)

def inputFold (key : VerifyingKey) (signals : Array Nat) (first : Affine) : Except String Jacobian :=
  (List.range' 0 signals.size).foldlM (inputStep key signals) (Jacobian.ofAffine first)

theorem input_forIn_fold (key : VerifyingKey) (signals : Array Nat) (indices : List Nat) (state : Jacobian) :
    forIn indices state (fun index state => ForInStep.yield <$> inputStep key signals state index) =
      indices.foldlM (inputStep key signals) state := by simp

theorem input_candidate_source (key : VerifyingKey) (signals : Array Nat) :
    nativeInputCandidate key signals = (do
      if key.ic.size != signals.size + 1 || signals.size > maxPublicSignals then
        throw "Groth16 verifier dimensions or public-signal limit differ."
      if !key.ic.all (·.onCurve) then throw "Groth16 verification-key IC point is off-curve."
      let some first := key.ic[0]? | throw "Groth16 verification key has no IC origin."
      let sum ← inputFold key signals first
      let some value ← sum.toAffine | throw "Groth16 public-input commitment is infinity."
      return value) := by
  change (do
    if key.ic.size != signals.size + 1 || signals.size > maxPublicSignals then
      throw "Groth16 verifier dimensions or public-signal limit differ."
    if !key.ic.all (·.onCurve) then throw "Groth16 verification-key IC point is off-curve."
    let some first := key.ic[0]? | throw "Groth16 verification key has no IC origin."
    let mut sum := Jacobian.ofAffine first
    for i in [0:signals.size] do
      let some point := key.ic[i+1]? | throw "Groth16 verification key is missing an IC point."
      sum := sum.add ((Jacobian.ofAffine point).scalarMul signals[i]!)
    let some value ← sum.toAffine | throw "Groth16 public-input commitment is infinity."
    return value : Except String Affine) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', pure_bind, bind_pure_comp]
  split
  · rfl
  · split
    · rfl
    · cases first : key.ic[0]? with
      | none => rfl
      | some origin =>
        dsimp only
        unfold inputFold
        rw [← input_forIn_fold]
        congr 1
        simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
        congr 1
        funext index state
        cases point : key.ic[index+1]? <;> simp [inputStep, point]
        all_goals rfl

end LeanCrypto.Proofs.NativeVerifier
#print axioms LeanCrypto.Proofs.NativeVerifier.input_forIn_fold
#print axioms LeanCrypto.Proofs.NativeVerifier.input_candidate_source
