import Lean
import LeanCrypto.BN254.Constants

/-!
Native BN254 base-field and G1 arithmetic for explicit BN254 proof operations.
This is variable-time bigint code. Its public-point tests do not establish
side-channel resistance or secret erasure.
-/

namespace LeanCrypto.BN254.G1

def basePrime : Nat := LeanCrypto.BN254.Constants.basePrime

def scalarPrime : Nat := LeanCrypto.BN254.Constants.scalarPrime

structure Fp where
  val : Nat
  bounded : val < basePrime

instance : Inhabited Fp where
  default := ⟨0, by decide⟩

instance : BEq Fp where
  beq left right := left.val == right.val

def Fp.ofNat (value : Nat) : Fp :=
  ⟨value % basePrime, Nat.mod_lt _ (by decide)⟩

def Fp.zero : Fp := Fp.ofNat 0
def Fp.one : Fp := Fp.ofNat 1

def Fp.add (left right : Fp) : Fp := Fp.ofNat (left.val + right.val)
def Fp.mul (left right : Fp) : Fp := Fp.ofNat (left.val * right.val)
def Fp.neg (value : Fp) : Fp := Fp.ofNat (basePrime - value.val)
def Fp.sub (left right : Fp) : Fp := left.add right.neg

/-- Total tail-recursive square-and-multiply. The exponent strictly halves
at each step; unlike an opaque while loop, its equations are kernel-visible. -/
def Fp.powLoop (base : Fp) (exponent : Nat) (accumulator : Fp) : Fp :=
  if zero : exponent = 0 then accumulator
  else Fp.powLoop (base.mul base) (exponent / 2)
    (if exponent % 2 = 1 then accumulator.mul base else accumulator)
termination_by exponent
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

def Fp.pow (value : Fp) (exponent : Nat) : Fp :=
  Fp.powLoop value exponent Fp.one

/-- Inversion is checked by multiplication rather than trusting Fermat's
    theorem as an axiom. Zero or an unexpected composite modulus fails. -/
def Fp.inverse (value : Fp) : Except String Fp :=
  if value == Fp.zero then .error "BN254 Fp zero has no inverse."
  else
    let candidate := value.pow (basePrime - 2)
    if value.mul candidate == Fp.one then .ok candidate
    else .error "BN254 Fp inverse check failed."

theorem fp_ofNat_bounded (value : Nat) : (Fp.ofNat value).val < basePrime :=
  (Fp.ofNat value).bounded

theorem fp_add_bounded (left right : Fp) : (left.add right).val < basePrime :=
  (left.add right).bounded

theorem fp_mul_bounded (left right : Fp) : (left.mul right).val < basePrime :=
  (left.mul right).bounded

/-- The checked inverse relation is a theorem about the executable guard,
    independent of any primality assumption for the modulus. -/
theorem fp_inverse_sound (value result : Fp)
    (h : value.inverse = .ok result) : value.mul result == Fp.one := by
  cases hz : value == Fp.zero with
  | true => simp [Fp.inverse, hz] at h
  | false =>
    cases hc : value.mul (value.pow (basePrime - 2)) == Fp.one with
    | false => simp [Fp.inverse, hz, hc] at h
    | true =>
      simp [Fp.inverse, hz, hc] at h
      cases h
      exact hc

structure Affine where
  x : Fp
  y : Fp

def Affine.onCurve (point : Affine) : Bool :=
  point.y.mul point.y == (((point.x.mul point.x).mul point.x).add (Fp.ofNat 3))

def Affine.checked (x y : Nat) : Except String Affine := do
  if x >= basePrime || y >= basePrime then
    throw "BN254 G1 coordinate is outside the base field."
  let point : Affine := ⟨Fp.ofNat x, Fp.ofNat y⟩
  if !point.onCurve then throw "BN254 G1 point is not on the curve."
  return point

structure Jacobian where
  x : Fp
  y : Fp
  z : Fp

def Jacobian.infinity : Jacobian := ⟨Fp.zero, Fp.one, Fp.zero⟩

def Jacobian.ofAffine (point : Affine) : Jacobian :=
  ⟨point.x, point.y, Fp.one⟩

def Jacobian.isInfinity (point : Jacobian) : Bool := point.z == Fp.zero

def Jacobian.double (point : Jacobian) : Jacobian := Id.run do
  if point.isInfinity || point.y == Fp.zero then return Jacobian.infinity
  let xx := point.x.mul point.x
  let yy := point.y.mul point.y
  let yyyy := yy.mul yy
  let s := (point.x.mul yy).mul (Fp.ofNat 4)
  let m := xx.mul (Fp.ofNat 3)
  let x := (m.mul m).sub (s.mul (Fp.ofNat 2))
  let y := (m.mul (s.sub x)).sub (yyyy.mul (Fp.ofNat 8))
  let z := (point.y.mul point.z).mul (Fp.ofNat 2)
  return ⟨x, y, z⟩

def Jacobian.add (left right : Jacobian) : Jacobian := Id.run do
  if left.isInfinity then return right
  if right.isInfinity then return left
  let z1z1 := left.z.mul left.z
  let z2z2 := right.z.mul right.z
  let u1 := left.x.mul z2z2
  let u2 := right.x.mul z1z1
  let s1 := (left.y.mul right.z).mul z2z2
  let s2 := (right.y.mul left.z).mul z1z1
  if u1 == u2 then
    if s1 == s2 then return left.double
    return Jacobian.infinity
  let h := u2.sub u1
  let r := s2.sub s1
  let hh := h.mul h
  let hhh := hh.mul h
  let v := u1.mul hh
  let x := ((r.mul r).sub hhh).sub (v.mul (Fp.ofNat 2))
  let y := (r.mul (v.sub x)).sub (s1.mul hhh)
  let z := (left.z.mul right.z).mul h
  return ⟨x, y, z⟩

/-- Total tail-recursive binary scalar multiplication. The accumulator
and factor follow the same add/double/halve order as the original while. -/
def Jacobian.scalarMulLoop (factor : Jacobian) (scalar : Nat) (accumulator : Jacobian) : Jacobian :=
  if zero : scalar = 0 then accumulator
  else Jacobian.scalarMulLoop factor.double (scalar / 2)
    (if scalar % 2 = 1 then accumulator.add factor else accumulator)
termination_by scalar
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

def Jacobian.scalarMul (point : Jacobian) (scalar : Nat) : Jacobian :=
  Jacobian.scalarMulLoop point (scalar % scalarPrime) Jacobian.infinity

def Jacobian.toAffine (point : Jacobian) : Except String (Option Affine) := do
  if point.isInfinity then return none
  let inverse ← point.z.inverse
  let square := inverse.mul inverse
  let cube := square.mul inverse
  let affine : Affine := ⟨point.x.mul square, point.y.mul cube⟩
  if !affine.onCurve then throw "BN254 G1 normalization produced an off-curve point."
  return some affine

def generator : Affine := ⟨Fp.one, Fp.ofNat 2⟩

end LeanCrypto.BN254.G1

#print axioms LeanCrypto.BN254.G1.fp_ofNat_bounded
#print axioms LeanCrypto.BN254.G1.fp_add_bounded
#print axioms LeanCrypto.BN254.G1.fp_mul_bounded
#print axioms LeanCrypto.BN254.G1.fp_inverse_sound
