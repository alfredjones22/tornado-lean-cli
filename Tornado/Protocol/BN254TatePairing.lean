import Tornado.Protocol.BN254PairingField

/-!
Reference reduced Tate pairing on BN254 using affine E(Fp12) arithmetic.
This slow implementation operates on public data. It is used by the native
Groth16 verifier and differs from the EIP-197 optimal Ate pairing.
-/

namespace Tornado.Protocol.BN254TatePairing

open Tornado.Protocol.BN254G1 Tornado.Protocol.BN254G2
open Tornado.Protocol.BN254PairingField

/-- The final exponent is an exact integer for the pinned BN254 parameters. -/
theorem finalExponent_divisible :
    (basePrime ^ 12 - 1) % scalarPrime = 0 := by decide

def embedFp (value : Fp) : Fp12 :=
  ⟨⟨⟨value, Fp.zero⟩, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩

def embedFp2 (value : Fp2) : Fp12 :=
  ⟨⟨value, Fp2.zero, Fp2.zero⟩, Fp6.zero⟩

structure Point where
  x : Fp12
  y : Fp12

def Point.onCurve (point : Point) : Bool :=
  point.y.square ==
    ((point.x.square.mul point.x).add (embedFp (Fp.ofNat 3)))

/-- Sextic-twist embedding: w²=v, w³=v*w and w⁶=9+i. -/
def embedG2 (point : Tornado.Protocol.BN254G2.Affine) : Point :=
  ⟨⟨⟨Fp2.zero, point.x, Fp2.zero⟩, Fp6.zero⟩,
   ⟨Fp6.zero, ⟨Fp2.zero, point.y, Fp2.zero⟩⟩⟩

def embedG1 (point : Tornado.Protocol.BN254G1.Affine) : Point :=
  ⟨embedFp point.x, embedFp point.y⟩

private def divide (numerator denominator : Fp12) : Except String Fp12 := do
  if denominator == Fp12.zero then
    throw "BN254 pairing line denominator is zero."
  return numerator.mul (← denominator.inverse)

private def lineAndSum (r s eval : Point) : Except String (Fp12 × Option Point) := do
  if r.x == s.x && r.y == s.y.neg then
    let vertical := eval.x.sub r.x
    if vertical == Fp12.zero then throw "BN254 vertical line evaluated to zero."
    return (vertical, none)
  let slope ← if r.x == s.x && r.y == s.y then
      divide ((r.x.square).mul (embedFp (Fp.ofNat 3)))
        (r.y.mul (embedFp (Fp.ofNat 2)))
    else divide (s.y.sub r.y) (s.x.sub r.x)
  let x3 := ((slope.square).sub r.x).sub s.x
  let y3 := (slope.mul (r.x.sub x3)).sub r.y
  let line := (eval.y.sub r.y).sub (slope.mul (eval.x.sub r.x))
  let value ← divide line (eval.x.sub x3)
  if value == Fp12.zero then throw "BN254 pairing line evaluated to zero."
  return (value, some ⟨x3,y3⟩)

/-- Miller f_{r,Q}(P) with the full vertical denominator, avoiding the
    specialized denominator-elimination assumptions of Ate implementations. -/
def miller (q p : Point) : Except String Fp12 := do
  if !q.onCurve || !p.onCurve then
    throw "BN254 pairing point is off E(Fp12)."
  let scalar := scalarPrime
  let bits := Nat.log2 scalar + 1
  let mut f := Fp12.one
  let mut r : Option Point := some q
  for step in [1:bits] do
    let some current := r
      | throw "BN254 Miller accumulator reached infinity early."
    let (doubled, doubledPoint) ← lineAndSum current current p
    f := (f.square).mul doubled
    r := doubledPoint
    let bit := scalar / 2 ^ (bits - step - 1) % 2
    if bit == 1 then
      let some current := r
        | throw "BN254 Miller accumulator reached infinity before addition."
      let (added, addedPoint) ← lineAndSum current q p
      f := f.mul added
      r := addedPoint
  if r.isSome then throw "BN254 Miller scalar did not reach infinity."
  return f

/-- Candidate reduced Tate pairing. All input checks and arithmetic occur here;
    `pair` below verifies the output shape before exposing it. -/
private def pairCandidate (g1 : Tornado.Protocol.BN254G1.Affine)
    (g2 : Tornado.Protocol.BN254G2.Affine) : Except String Fp12 := do
  if !g1.onCurve || !g2.onCurve then
    throw "BN254 pairing input is off-curve."
  if !((Tornado.Protocol.BN254G2.Jacobian.ofAffine g2).scalarMul scalarPrime).isInfinity then
    throw "BN254 G2 point is outside the prime-order subgroup."
  let value ← miller (embedG2 g2) (embedG1 g1)
  return value.pow ((basePrime ^ 12 - 1) / scalarPrime)

/-- Reduced Tate pairing with explicit nonzero and r-torsion output checks.
    The checks are proved below; the Miller algorithm itself is not proved
    equivalent to the mathematical Tate pairing. -/
def pair (g1 : Tornado.Protocol.BN254G1.Affine)
    (g2 : Tornado.Protocol.BN254G2.Affine) : Except String Fp12 :=
  match pairCandidate g1 g2 with
  | .error message => .error message
  | .ok final =>
      if final == Fp12.zero then
        .error "BN254 Tate pairing final exponent result was zero."
      else if final.pow scalarPrime == Fp12.one then
        .ok final
      else .error "BN254 Tate pairing final exponent order check failed."

theorem pair_success_nonzero (g1 : Tornado.Protocol.BN254G1.Affine)
    (g2 : Tornado.Protocol.BN254G2.Affine) (result : Fp12)
    (h : pair g1 g2 = .ok result) : result != Fp12.zero := by
  unfold pair at h
  cases hc : pairCandidate g1 g2 with
  | error _ => simp [hc] at h
  | ok candidate =>
      simp only [hc] at h
      split at h
      · simp at h
      · rename_i hnonzero
        split at h
        · cases h
          cases hb : result == Fp12.zero with
          | false => simp [bne, hb]
          | true => exact False.elim (hnonzero hb)
        · simp at h

theorem pair_success_order (g1 : Tornado.Protocol.BN254G1.Affine)
    (g2 : Tornado.Protocol.BN254G2.Affine) (result : Fp12)
    (h : pair g1 g2 = .ok result) : result.pow scalarPrime == Fp12.one := by
  unfold pair at h
  cases hc : pairCandidate g1 g2 with
  | error _ => simp [hc] at h
  | ok candidate =>
      simp only [hc] at h
      split at h
      · simp at h
      · split at h
        · rename_i horder
          cases h
          exact horder
        · simp at h

end Tornado.Protocol.BN254TatePairing

#print axioms Tornado.Protocol.BN254TatePairing.pair_success_nonzero
#print axioms Tornado.Protocol.BN254TatePairing.pair_success_order
#print axioms Tornado.Protocol.BN254TatePairing.finalExponent_divisible
