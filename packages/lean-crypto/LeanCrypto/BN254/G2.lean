import LeanCrypto.BN254.G1

/-!
Native quadratic extension field and BN254 G2 point arithmetic. This is a
variable-time building block for explicit BN254 proof operations, not a pairing or
subgroup verifier. It must not process funded-note scalars yet.
-/

namespace LeanCrypto.BN254.G2

open LeanCrypto.BN254.G1

structure Fp2 where
  c0 : Fp
  c1 : Fp

instance : Inhabited Fp2 where
  default := ⟨Fp.zero, Fp.zero⟩

instance : BEq Fp2 where
  beq left right := left.c0 == right.c0 && left.c1 == right.c1

def Fp2.zero : Fp2 := ⟨Fp.zero, Fp.zero⟩
def Fp2.one : Fp2 := ⟨Fp.one, Fp.zero⟩
def Fp2.ofNats (real imaginary : Nat) : Fp2 :=
  ⟨Fp.ofNat real, Fp.ofNat imaginary⟩

def Fp2.add (left right : Fp2) : Fp2 :=
  ⟨left.c0.add right.c0, left.c1.add right.c1⟩
def Fp2.neg (value : Fp2) : Fp2 :=
  ⟨value.c0.neg, value.c1.neg⟩
def Fp2.sub (left right : Fp2) : Fp2 := left.add right.neg
def Fp2.mul (left right : Fp2) : Fp2 :=
  ⟨(left.c0.mul right.c0).sub (left.c1.mul right.c1),
   (left.c0.mul right.c1).add (left.c1.mul right.c0)⟩

def Fp2.inverse (value : Fp2) : Except String Fp2 := do
  let denominator := (value.c0.mul value.c0).add (value.c1.mul value.c1)
  let inverse ← denominator.inverse
  let result : Fp2 := ⟨value.c0.mul inverse, value.c1.neg.mul inverse⟩
  if value.mul result != Fp2.one then
    throw "BN254 Fp2 inverse check failed."
  return result

def twistB : Fp2 := Fp2.ofNats
  19485874751759354771024239261021720505790618469301721065564631296452457478373
  266929791119991161246907387137283842545076965332900288569378510910307636690

structure Affine where
  x : Fp2
  y : Fp2

def Affine.onCurve (point : Affine) : Bool :=
  point.y.mul point.y == (((point.x.mul point.x).mul point.x).add twistB)

def Affine.checked (x0 x1 y0 y1 : Nat) : Except String Affine := do
  if x0 >= basePrime || x1 >= basePrime || y0 >= basePrime || y1 >= basePrime then
    throw "BN254 G2 coordinate is outside the base field."
  let point : Affine := ⟨Fp2.ofNats x0 x1, Fp2.ofNats y0 y1⟩
  if !point.onCurve then throw "BN254 G2 point is not on the twist."
  return point

structure Jacobian where
  x : Fp2
  y : Fp2
  z : Fp2

def Jacobian.infinity : Jacobian := ⟨Fp2.zero, Fp2.one, Fp2.zero⟩
def Jacobian.ofAffine (point : Affine) : Jacobian := ⟨point.x, point.y, Fp2.one⟩
def Jacobian.isInfinity (point : Jacobian) : Bool := point.z == Fp2.zero

def Jacobian.double (point : Jacobian) : Jacobian := Id.run do
  if point.isInfinity || point.y == Fp2.zero then return Jacobian.infinity
  let xx := point.x.mul point.x
  let yy := point.y.mul point.y
  let yyyy := yy.mul yy
  let s := (point.x.mul yy).mul (Fp2.ofNats 4 0)
  let m := xx.mul (Fp2.ofNats 3 0)
  let x := (m.mul m).sub (s.mul (Fp2.ofNats 2 0))
  let y := (m.mul (s.sub x)).sub (yyyy.mul (Fp2.ofNats 8 0))
  let z := (point.y.mul point.z).mul (Fp2.ofNats 2 0)
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
  let x := ((r.mul r).sub hhh).sub (v.mul (Fp2.ofNats 2 0))
  let y := (r.mul (v.sub x)).sub (s1.mul hhh)
  let z := (left.z.mul right.z).mul h
  return ⟨x, y, z⟩

/-- This intentionally does not reduce the scalar modulo Fr: a later
    subgroup checker can test `[Fr]P = 0` without making that check vacuous. -/
def Jacobian.scalarMul (point : Jacobian) (scalar : Nat) : Jacobian := Id.run do
  let mut factor := point
  let mut n := scalar
  let mut result := Jacobian.infinity
  while n > 0 do
    if n % 2 == 1 then result := result.add factor
    factor := factor.double
    n := n / 2
  return result

def Jacobian.toAffine (point : Jacobian) : Except String (Option Affine) := do
  if point.isInfinity then return none
  let inverse ← point.z.inverse
  let square := inverse.mul inverse
  let cube := square.mul inverse
  let affine : Affine := ⟨point.x.mul square, point.y.mul cube⟩
  if !affine.onCurve then throw "BN254 G2 normalization produced an off-twist point."
  return some affine

def generator : Affine := ⟨
  Fp2.ofNats
    10857046999023057135944570762232829481370756359578518086990519993285655852781
    11559732032986387107991004021392285783925812861821192530917403151452391805634,
  Fp2.ofNats
    8495653923123431417604973247489272438418190587263600148770280649306958101930
    4082367875863433681332203403145435568316851327593401208105741076214120093531⟩

end LeanCrypto.BN254.G2
