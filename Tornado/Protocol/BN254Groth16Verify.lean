import Tornado.Protocol.BN254TatePairing

/-!
Native Groth16 verification equation over BN254 for public proof points.
The caller must supply an authenticated verification key. Pairing arithmetic is
the slow reduced Tate reference, not the EIP-197 optimal Ate implementation.
The two pairings define the same yes/no equation for prime-order G1/G2 points,
but this correspondence is not proved in Lean. This module does not prove
Groth16 soundness or that the external circuit has the intended semantics.
-/

namespace Tornado.Protocol.BN254Groth16Verify

open Tornado.Protocol.BN254G1 Tornado.Protocol.BN254G2
open Tornado.Protocol.BN254PairingField
open Tornado.Protocol.BN254TatePairing

structure VerifyingKey where
  alpha1 : Tornado.Protocol.BN254G1.Affine
  beta2 : Tornado.Protocol.BN254G2.Affine
  gamma2 : Tornado.Protocol.BN254G2.Affine
  delta2 : Tornado.Protocol.BN254G2.Affine
  ic : Array Tornado.Protocol.BN254G1.Affine

structure Proof where
  a : Tornado.Protocol.BN254G1.Affine
  b : Tornado.Protocol.BN254G2.Affine
  c : Tornado.Protocol.BN254G1.Affine

private def publicInputPointCandidate (key : VerifyingKey) (signals : Array Nat) :
    Except String Tornado.Protocol.BN254G1.Affine := do
  if key.ic.size != signals.size + 1 || signals.size != 6 then
    throw "Classic Groth16 verifier needs seven IC points and six public signals."
  if !key.ic.all (·.onCurve) then
    throw "Classic Groth16 verification-key IC point is off-curve."
  let some first := key.ic[0]?
    | throw "Classic Groth16 verification key has no IC origin."
  let mut sum := Tornado.Protocol.BN254G1.Jacobian.ofAffine first
  for i in [0:6] do
    let some point := key.ic[i+1]?
      | throw "Classic Groth16 verification key is missing an IC point."
    sum := sum.add ((Tornado.Protocol.BN254G1.Jacobian.ofAffine point).scalarMul signals[i]!)
  let some value ← sum.toAffine
    | throw "Classic Groth16 public-input commitment is infinity."
  return value

/-- The public-input commitment is only exposed for canonical Fr signals. -/
def publicInputPoint (key : VerifyingKey) (signals : Array Nat) :
    Except String Tornado.Protocol.BN254G1.Affine :=
  if signals.all (· < scalarPrime) then
    publicInputPointCandidate key signals
  else .error "Classic Groth16 public signal is outside BN254 Fr."

theorem publicInputPoint_success_signals_bounded (key : VerifyingKey)
    (signals : Array Nat) (result : Tornado.Protocol.BN254G1.Affine)
    (h : publicInputPoint key signals = .ok result) :
    signals.all (· < scalarPrime) = true := by
  unfold publicInputPoint at h
  cases hb : signals.all (· < scalarPrime) with
  | false => simp [hb] at h
  | true => rfl

/-- Return false for a well-formed but invalid proof equation; malformed points,
    bad subgroup membership, and pairing failures return an error. -/
def verify (key : VerifyingKey) (proof : Proof) (signals : Array Nat) :
    Except String Bool := do
  let vkX ← publicInputPoint key signals
  let negativeA : Tornado.Protocol.BN254G1.Affine := ⟨proof.a.x, proof.a.y.neg⟩
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

end Tornado.Protocol.BN254Groth16Verify

#print axioms Tornado.Protocol.BN254Groth16Verify.publicInputPoint_success_signals_bounded
#print axioms Tornado.Protocol.BN254Groth16Verify.verify_true_signals_bounded
