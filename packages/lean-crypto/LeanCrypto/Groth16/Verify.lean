import LeanCrypto.BN254.TatePairing

/-!
Native Groth16 verification equation over BN254 for public proof points.
The caller must supply an authenticated verification key. Pairing arithmetic is
the slow reduced Tate reference, not the EIP-197 optimal Ate implementation.
The two pairings define the same yes/no equation for prime-order G1/G2 points,
but this correspondence is not proved in Lean. Affine proof points and
public-input commitments at infinity are deliberately rejected, preserving
the reference policy. Zero public signals are allowed with exactly one IC
point. Every proof/key G2 point passes the pairing subgroup guard. This module does not prove
Groth16 soundness or that the external circuit has the intended semantics.
-/

namespace LeanCrypto.Groth16.Verify

open LeanCrypto.BN254.G1 LeanCrypto.BN254.G2
open LeanCrypto.BN254.PairingField
open LeanCrypto.BN254.TatePairing

/-- Public-input resource bound, independent of a particular circuit. -/
def maxPublicSignals : Nat := 1024

structure VerifyingKey where
  alpha1 : LeanCrypto.BN254.G1.Affine
  beta2 : LeanCrypto.BN254.G2.Affine
  gamma2 : LeanCrypto.BN254.G2.Affine
  delta2 : LeanCrypto.BN254.G2.Affine
  ic : Array LeanCrypto.BN254.G1.Affine

structure Proof where
  a : LeanCrypto.BN254.G1.Affine
  b : LeanCrypto.BN254.G2.Affine
  c : LeanCrypto.BN254.G1.Affine

private def publicInputPointCandidate (key : VerifyingKey) (signals : Array Nat) :
    Except String LeanCrypto.BN254.G1.Affine := do
  if key.ic.size != signals.size + 1 || signals.size > maxPublicSignals then
    throw "Groth16 verifier dimensions or public-signal limit differ."
  if !key.ic.all (·.onCurve) then
    throw "Groth16 verification-key IC point is off-curve."
  let some first := key.ic[0]?
    | throw "Groth16 verification key has no IC origin."
  let mut sum := LeanCrypto.BN254.G1.Jacobian.ofAffine first
  for i in [0:signals.size] do
    let some point := key.ic[i+1]?
      | throw "Groth16 verification key is missing an IC point."
    sum := sum.add ((LeanCrypto.BN254.G1.Jacobian.ofAffine point).scalarMul signals[i]!)
  let some value ← sum.toAffine
    | throw "Groth16 public-input commitment is infinity."
  return value

/-- The public-input commitment is only exposed for canonical Fr signals. -/
def publicInputPoint (key : VerifyingKey) (signals : Array Nat) :
    Except String LeanCrypto.BN254.G1.Affine :=
  if signals.all (· < scalarPrime) then
    publicInputPointCandidate key signals
  else .error "Groth16 public signal is outside BN254 Fr."

theorem publicInputPoint_success_signals_bounded (key : VerifyingKey)
    (signals : Array Nat) (result : LeanCrypto.BN254.G1.Affine)
    (h : publicInputPoint key signals = .ok result) :
    signals.all (· < scalarPrime) = true := by
  unfold publicInputPoint at h
  cases hb : signals.all (· < scalarPrime) with
  | false => simp [hb] at h
  | true => rfl

theorem publicInputPoint_success_dimensions (key : VerifyingKey) (signals : Array Nat)
    (result : LeanCrypto.BN254.G1.Affine) (h : publicInputPoint key signals = .ok result) :
    key.ic.size = signals.size + 1 ∧ signals.size ≤ maxPublicSignals := by
  cases canonical : signals.all (· < scalarPrime) with
  | false => simp [publicInputPoint, canonical] at h
  | true =>
    have candidate : publicInputPointCandidate key signals = .ok result := by
      simpa [publicInputPoint, canonical] using h
    by_cases count : key.ic.size = signals.size + 1
    · refine ⟨count, ?_⟩
      by_cases bounded : signals.size ≤ maxPublicSignals
      · exact bounded
      · have high : signals.size > maxPublicSignals := Nat.lt_of_not_ge bounded
        simp [publicInputPointCandidate, count, high, bind, Except.bind] at candidate
    · simp [publicInputPointCandidate, count, bind, Except.bind] at candidate

/-- Return false for a well-formed but invalid proof equation; malformed points,
    bad subgroup membership, and pairing failures return an error. -/
def verify (key : VerifyingKey) (proof : Proof) (signals : Array Nat) :
    Except String Bool := do
  let vkX ← publicInputPoint key signals
  let negativeA : LeanCrypto.BN254.G1.Affine := ⟨proof.a.x, proof.a.y.neg⟩
  let e0 ← pair negativeA proof.b
  let e1 ← pair key.alpha1 key.beta2
  let e2 ← pair vkX key.gamma2
  let e3 ← pair proof.c key.delta2
  return (((e0.mul e1).mul e2).mul e3) == Fp12.one

/-- Even a caller-supplied key cannot make the executable verifier accept an
    out-of-field public signal. This is a guard theorem, not Groth16 soundness. -/
theorem verify_true_signals_bounded (key : VerifyingKey) (proof : Proof)
    (signals : Array Nat) (h : verify key proof signals = .ok true) :
    signals.all (· < scalarPrime) = true := by
  cases hp : publicInputPoint key signals with
  | error err =>
      have he : verify key proof signals = .error err := by
        unfold verify
        rw [hp]
        rfl
      rw [he] at h
      cases h
  | ok point => exact publicInputPoint_success_signals_bounded key signals point hp

theorem verify_true_dimensions (key : VerifyingKey) (proof : Proof) (signals : Array Nat)
    (h : verify key proof signals = .ok true) :
    key.ic.size = signals.size + 1 ∧ signals.size ≤ maxPublicSignals := by
  cases point : publicInputPoint key signals with
  | error message =>
    have rejected : verify key proof signals = .error message := by
      unfold verify
      rw [point]
      rfl
    rw [rejected] at h
    cases h
  | ok value => exact publicInputPoint_success_dimensions key signals value point

end LeanCrypto.Groth16.Verify

#print axioms LeanCrypto.Groth16.Verify.publicInputPoint_success_signals_bounded
#print axioms LeanCrypto.Groth16.Verify.verify_true_signals_bounded

#print axioms LeanCrypto.Groth16.Verify.publicInputPoint_success_dimensions
#print axioms LeanCrypto.Groth16.Verify.verify_true_dimensions
