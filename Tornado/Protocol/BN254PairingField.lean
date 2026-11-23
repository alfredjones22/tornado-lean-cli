import Tornado.Protocol.BN254G2

/-!
BN254 extension-field tower used by the optimal Ate pairing. This module
implements field arithmetic only: Fp6 = Fp2[v] / (v^3 - (9+i)), and
Fp12 = Fp6[w] / (w^2-v). It does not implement Miller loops, final
exponentiation, subgroup checks, or Groth16 verification.

All big-integer operations are variable-time and are for public points only.
-/

namespace Tornado.Protocol.BN254PairingField

open Tornado.Protocol.BN254G2

def nonresidue : Fp2 := Fp2.ofNats 9 1

structure Fp6 where
  c0 : Fp2
  c1 : Fp2
  c2 : Fp2

instance : Inhabited Fp6 := ⟨⟨Fp2.zero, Fp2.zero, Fp2.zero⟩⟩
instance : BEq Fp6 where
  beq left right := left.c0 == right.c0 && left.c1 == right.c1 &&
    left.c2 == right.c2

def Fp6.zero : Fp6 := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩
def Fp6.one : Fp6 := ⟨Fp2.one, Fp2.zero, Fp2.zero⟩
def Fp6.v : Fp6 := ⟨Fp2.zero, Fp2.one, Fp2.zero⟩

def Fp6.add (a b : Fp6) : Fp6 :=
  ⟨a.c0.add b.c0, a.c1.add b.c1, a.c2.add b.c2⟩
def Fp6.neg (a : Fp6) : Fp6 :=
  ⟨a.c0.neg, a.c1.neg, a.c2.neg⟩
def Fp6.sub (a b : Fp6) : Fp6 := a.add b.neg

/-- Multiplication by v maps (a0,a1,a2) to (ξ a2,a0,a1). -/
def Fp6.mulByV (a : Fp6) : Fp6 :=
  ⟨nonresidue.mul a.c2, a.c0, a.c1⟩

/-- Direct polynomial multiplication modulo v³=9+i. -/
def Fp6.mul (a b : Fp6) : Fp6 :=
  ⟨(a.c0.mul b.c0).add (nonresidue.mul
      ((a.c1.mul b.c2).add (a.c2.mul b.c1))),
   ((a.c0.mul b.c1).add (a.c1.mul b.c0)).add
      (nonresidue.mul (a.c2.mul b.c2)),
   ((a.c0.mul b.c2).add (a.c1.mul b.c1)).add (a.c2.mul b.c0)⟩

/-- Checked inversion in Fp6. The cofactor construction is verified by
    multiplying the candidate back to one. -/
private def Fp6.inverseCandidate (a : Fp6) : Except String Fp6 := do
  if a == Fp6.zero then throw "BN254 Fp6 zero has no inverse."
  let t0 := (a.c0.mul a.c0).sub
    (nonresidue.mul (a.c1.mul a.c2))
  let t1 := (nonresidue.mul (a.c2.mul a.c2)).sub
    (a.c0.mul a.c1)
  let t2 := (a.c1.mul a.c1).sub (a.c0.mul a.c2)
  let den := (a.c0.mul t0).add (nonresidue.mul
    ((a.c2.mul t1).add (a.c1.mul t2)))
  let inv ← den.inverse
  return ⟨t0.mul inv, t1.mul inv, t2.mul inv⟩

def Fp6.inverse (a : Fp6) : Except String Fp6 :=
  match a.inverseCandidate with
  | .error message => .error message
  | .ok result =>
      if a.mul result == Fp6.one then .ok result
      else .error "BN254 Fp6 inverse check failed."

structure Fp12 where
  c0 : Fp6
  c1 : Fp6

instance : Inhabited Fp12 := ⟨⟨Fp6.zero, Fp6.zero⟩⟩
instance : BEq Fp12 where
  beq left right := left.c0 == right.c0 && left.c1 == right.c1

def Fp12.zero : Fp12 := ⟨Fp6.zero, Fp6.zero⟩
def Fp12.one : Fp12 := ⟨Fp6.one, Fp6.zero⟩
def Fp12.w : Fp12 := ⟨Fp6.zero, Fp6.one⟩

def Fp12.add (a b : Fp12) : Fp12 :=
  ⟨a.c0.add b.c0, a.c1.add b.c1⟩
def Fp12.neg (a : Fp12) : Fp12 :=
  ⟨a.c0.neg, a.c1.neg⟩
def Fp12.sub (a b : Fp12) : Fp12 := a.add b.neg
def Fp12.conjugate (a : Fp12) : Fp12 := ⟨a.c0, a.c1.neg⟩

/-- Multiplication modulo w²=v. -/
def Fp12.mul (a b : Fp12) : Fp12 :=
  ⟨(a.c0.mul b.c0).add ((a.c1.mul b.c1).mulByV),
   (a.c0.mul b.c1).add (a.c1.mul b.c0)⟩

def Fp12.square (a : Fp12) : Fp12 := a.mul a

def Fp12.pow (a : Fp12) (exponent : Nat) : Fp12 := Id.run do
  let mut n := exponent
  let mut base := a
  let mut result := Fp12.one
  while n > 0 do
    if n % 2 == 1 then result := result.mul base
    base := base.square
    n := n / 2
  return result

/-- Checked inversion in Fp12; no unproved primality axiom is used. -/
private def Fp12.inverseCandidate (a : Fp12) : Except String Fp12 := do
  if a == Fp12.zero then throw "BN254 Fp12 zero has no inverse."
  let den := (a.c0.mul a.c0).sub ((a.c1.mul a.c1).mulByV)
  let inv ← den.inverse
  return ⟨a.c0.mul inv, a.c1.neg.mul inv⟩

def Fp12.inverse (a : Fp12) : Except String Fp12 :=
  match a.inverseCandidate with
  | .error message => .error message
  | .ok result =>
      if a.mul result == Fp12.one then .ok result
      else .error "BN254 Fp12 inverse check failed."

theorem fp6_inverse_sound (a result : Fp6)
    (h : a.inverse = .ok result) : a.mul result == Fp6.one := by
  unfold Fp6.inverse at h
  cases hc : a.inverseCandidate with
  | error _ => simp [hc] at h
  | ok candidate =>
      simp only [hc] at h
      split at h
      · rename_i good
        cases h
        exact good
      · simp at h

theorem fp12_inverse_sound (a result : Fp12)
    (h : a.inverse = .ok result) : a.mul result == Fp12.one := by
  unfold Fp12.inverse at h
  cases hc : a.inverseCandidate with
  | error _ => simp [hc] at h
  | ok candidate =>
      simp only [hc] at h
      split at h
      · rename_i good
        cases h
        exact good
      · simp at h

end Tornado.Protocol.BN254PairingField

#print axioms Tornado.Protocol.BN254PairingField.fp6_inverse_sound
#print axioms Tornado.Protocol.BN254PairingField.fp12_inverse_sound
