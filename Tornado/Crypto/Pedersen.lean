import Tornado.Crypto.Blake256

/-!
Classic Tornado Pedersen hash over BabyJubJub, matching the pinned
`micro-zk-proofs/pedersen.js` implementation. This includes its unusual
BLAKE-256 generator search, lower-root point decoding, 25-byte signed-window
scalar layout, and point encoding convention. It is pure Lean.

This is a compatibility implementation, not a cryptographic proof. The
variable-time field inversion, square root, and scalar multiplication mean it
must not be advertised as constant-time. `pedersenHash` returns an error if
generator search exceeds a generous 1024 attempts or a point is invalid.
-/

namespace Tornado.Crypto

private def fieldPrime : Nat :=
  0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

private def subgroupOrder : Nat :=
  0x060c89ce5c263405370a08b6d0302b0bab3eedb83920ee0a677297dc392126f1

private def curveA : Nat := 168700
private def curveD : Nat := 168696

private def fadd (x y : Nat) : Nat := (x + y) % fieldPrime
private def fsub (x y : Nat) : Nat := (x + fieldPrime - y % fieldPrime) % fieldPrime
private def fmul (x y : Nat) : Nat := (x * y) % fieldPrime

private def powMod (base exponent : Nat) : Nat := Id.run do
  let mut result := 1
  let mut x := base % fieldPrime
  let mut n := exponent
  while n > 0 do
    if n % 2 == 1 then result := fmul result x
    x := fmul x x
    n := n / 2
  return result

private def finv (x : Nat) : Option Nat :=
  if x % fieldPrime == 0 then none
  else some (powMod x (fieldPrime - 2))

-- Generic Tonelli-Shanks over the fixed odd BabyJubJub prime. The chosen
-- square root is later canonicalized to the lower of the two roots.
private def sqrtMod (value : Nat) : Option Nat := Id.run do
  let n := value % fieldPrime
  if n == 0 then return some 0
  if powMod n ((fieldPrime - 1) / 2) != 1 then return none
  let mut q := fieldPrime - 1
  let mut s := 0
  while q % 2 == 0 do
    q := q / 2
    s := s + 1
  let mut z := 2
  while powMod z ((fieldPrime - 1) / 2) != fieldPrime - 1 do
    z := z + 1
  let mut c := powMod z q
  let mut r := powMod n ((q + 1) / 2)
  let mut t := powMod n q
  let mut m := s
  while t != 1 do
    let mut i := 1
    let mut t2 := fmul t t
    while i < m && t2 != 1 do
      t2 := fmul t2 t2
      i := i + 1
    if i >= m then return none
    let b := powMod c (2 ^ (m - i - 1))
    r := fmul r b
    c := fmul b b
    t := fmul t c
    m := i
  return some (min r (fsub 0 r))

private structure ExtendedPoint where
  x : Nat
  y : Nat
  z : Nat
  t : Nat
  deriving Repr

private def identity : ExtendedPoint := ⟨0, 1, 1, 0⟩

private def ofAffine (x y : Nat) : ExtendedPoint :=
  ⟨x, y, 1, fmul x y⟩

private def addPoints (p q : ExtendedPoint) : ExtendedPoint :=
  let a := fmul p.x q.x
  let b := fmul p.y q.y
  let c := fmul (fmul curveD p.t) q.t
  let d := fmul p.z q.z
  let e := fsub (fsub (fmul (fadd p.x p.y) (fadd q.x q.y)) a) b
  let f := fsub d c
  let g := fadd d c
  let h := fsub b (fmul curveA a)
  ⟨fmul e f, fmul g h, fmul f g, fmul e h⟩

private def scalarMul (point : ExtendedPoint) (scalar : Nat) : ExtendedPoint := Id.run do
  let mut result := identity
  let mut base := point
  let mut n := scalar
  while n > 0 do
    if n % 2 == 1 then result := addPoints result base
    base := addPoints base base
    n := n / 2
  return result

private def affine (point : ExtendedPoint) : Option (Nat × Nat) := do
  let invZ ← finv point.z
  let x := fmul point.x invZ
  let y := fmul point.y invZ
  let x2 := fmul x x
  let y2 := fmul y y
  if fadd (fmul curveA x2) y2 != fadd 1 (fmul curveD (fmul x2 y2)) then none
  else some (x, y)

private def fromLE (bytes : ByteArray) : Nat := Id.run do
  let mut value := 0
  let mut power := 1
  for byte in bytes.data do
    value := value + byte.toNat * power
    power := power * 256
  return value

private def toLE32 (value : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut n := value
  for _ in [0:32] do
    out := out.push (UInt8.ofNat (n % 256))
    n := n / 256
  return out

private def decodePoint (bytes : ByteArray) : Option ExtendedPoint := do
  if bytes.size != 32 then none else do
    let sign := (bytes.get! 31).toNat / 128 == 1
    let normed := bytes.set! 31 ((bytes.get! 31) &&& (0x7f : UInt8))
    let y := fromLE normed
    if y >= fieldPrime then none else do
      let y2 := fmul y y
      let numerator := fsub 1 y2
      let denominator := fsub curveA (fmul curveD y2)
      let inv ← finv denominator
      let x2 := fmul numerator inv
      let lower ← sqrtMod x2
      let x := if sign then fsub 0 lower else lower
      some (ofAffine x y)

private def encodePoint (point : ExtendedPoint) : Option ByteArray := do
  let (x, y) ← affine point
  let mut bytes := toLE32 y
  if x > fieldPrime / 2 then
    bytes := bytes.set! 31 ((bytes.get! 31) ||| (0x80 : UInt8))
  some bytes

private def pad32 (value : Nat) : String :=
  let digits := toString value
  String.ofList (List.replicate (32 - digits.length) '0') ++ digits

private def generator (index : Nat) : Except String ExtendedPoint := Id.run do
  for attempt in [0:1024] do
    let label := s!"PedersenGenerator_{pad32 index}_{pad32 attempt}"
    let digest := blake256 label.toUTF8
    -- Mirrors `h[31] &= 0b1011_1111` in micro-zk-proofs.
    let candidate := digest.set! 31 ((digest.get! 31) &&& (0xbf : UInt8))
    if let some point := decodePoint candidate then
      let cleared := scalarMul point 8
      if let some (x, y) := affine cleared then
        if x != 0 || y != 1 then return .ok cleared
  return .error s!"BabyJubJub generator {index} was not found in 1024 attempts"

private def signedNibble (digit : Nat) : Int :=
  let absolute := Int.ofNat (digit % 8 + 1)
  if digit >= 8 then -absolute else absolute

private def chunkScalar (bytes : ByteArray) : Nat := Id.run do
  let mut signed : Int := 0
  let mut weight : Int := 1
  for byte in bytes.data do
    let n := byte.toNat
    signed := signed + signedNibble (n % 16) * weight
    weight := weight * 32
    signed := signed + signedNibble (n / 16) * weight
    weight := weight * 32
  if signed < 0 then signed := signed + Int.ofNat subgroupOrder
  return signed.toNat

/-- Encode the Pedersen hash point for arbitrary bytes. The note protocol
    passes exactly 31 bytes for a nullifier hash and 62 for a commitment. -/
def pedersenHash (input : ByteArray) : Except String ByteArray := do
  let mut result := identity
  let chunks := (input.size + 24) / 25
  for i in [0:chunks] do
    let point ← generator i
    let scalar := chunkScalar (input.extract (i * 25) (min ((i + 1) * 25) input.size))
    if scalar == 0 || scalar >= subgroupOrder then
      throw s!"Invalid Pedersen scalar for chunk {i}"
    result := addPoints result (scalarMul point scalar)
  match encodePoint result with
  | some bytes => return bytes
  | none => throw "Invalid Pedersen result"

/-- The x-coordinate extracted by Classic Tornado from the encoded hash. -/
def pedersenX (input : ByteArray) : Except String Nat := do
  let bytes ← pedersenHash input
  match decodePoint bytes with
  | some point =>
    match affine point with
    | some (x, _) => return x
    | none => throw "Invalid decoded Pedersen result"
  | none => throw "Invalid encoded Pedersen result"

end Tornado.Crypto
