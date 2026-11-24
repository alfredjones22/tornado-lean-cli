import LeanCrypto.SHA256
import LeanCrypto.Constants
import LeanCrypto.Keccak

/-!
Pure Lean secp256k1 point multiplication and deterministic ECDSA signing.
The nonce follows RFC 6979 HMAC-SHA256, with low-S normalization matching
viem/@noble/curves. Lean's arbitrary-precision natural-number arithmetic is
not constant-time; this implementation is compatibility work, not hardened
against local timing or memory-observation attacks.
-/

namespace LeanCrypto

def secp256k1FieldPrime : Nat :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

private def secpGx : Nat :=
  0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798

private def secpGy : Nat :=
  0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

private def modAdd (a b : Nat) : Nat := (a + b) % secp256k1FieldPrime
private def modMul (a b : Nat) : Nat := (a * b) % secp256k1FieldPrime
private def modSub (a b : Nat) : Nat :=
  (a + secp256k1FieldPrime - b % secp256k1FieldPrime) % secp256k1FieldPrime

private def powMod (base exponent modulus : Nat) : Nat := Id.run do
  let mut result := 1
  let mut b := base % modulus
  let mut e := exponent
  while e > 0 do
    if e % 2 == 1 then result := (result * b) % modulus
    b := (b * b) % modulus
    e := e / 2
  return result

private def inversePrime (n prime : Nat) : Nat :=
  powMod n (prime - 2) prime

structure SecpAffine where
  x : Nat
  y : Nat
  infinity : Bool := false

private structure SecpJacobian where
  x : Nat
  y : Nat
  z : Nat

private def infinityJacobian : SecpJacobian := ⟨0, 1, 0⟩
private def basePoint : SecpAffine := ⟨secpGx, secpGy, false⟩

private def jacobianDouble (a : SecpJacobian) : SecpJacobian := Id.run do
  if a.z == 0 || a.y == 0 then return infinityJacobian
  let yy := modMul a.y a.y
  let yyyy := modMul yy yy
  let s := modMul 4 (modMul a.x yy)
  let m := modMul 3 (modMul a.x a.x)
  let x := modSub (modMul m m) (modMul 2 s)
  let y := modSub (modMul m (modSub s x)) (modMul 8 yyyy)
  let z := modMul 2 (modMul a.y a.z)
  return ⟨x, y, z⟩

private def jacobianAddAffine (a : SecpJacobian) (b : SecpAffine) : SecpJacobian := Id.run do
  if b.infinity then return a
  if a.z == 0 then return ⟨b.x, b.y, 1⟩
  let zz := modMul a.z a.z
  let u := modMul b.x zz
  let s := modMul b.y (modMul a.z zz)
  let h := modSub u a.x
  let r := modSub s a.y
  if h == 0 then
    if r == 0 then return jacobianDouble a
    else return infinityJacobian
  let hh := modMul h h
  let hhh := modMul hh h
  let v := modMul a.x hh
  let x := modSub (modSub (modMul r r) hhh) (modMul 2 v)
  let y := modSub (modMul r (modSub v x)) (modMul a.y hhh)
  let z := modMul a.z h
  return ⟨x, y, z⟩

private def jacobianToAffine (a : SecpJacobian) : SecpAffine := Id.run do
  if a.z == 0 then return ⟨0, 0, true⟩
  let iz := inversePrime a.z secp256k1FieldPrime
  let iz2 := modMul iz iz
  return ⟨modMul a.x iz2, modMul a.y (modMul iz2 iz), false⟩

/-- Scalar multiplication of the generator, using Jacobian coordinates. -/
def secp256k1BaseMul (scalar : Nat) : SecpAffine := Id.run do
  let mut result := infinityJacobian
  let k := scalar % secp256k1Order
  for i in [0:256] do
    result := jacobianDouble result
    if k / 2 ^ (255 - i) % 2 == 1 then
      result := jacobianAddAffine result basePoint
  return jacobianToAffine result

private def bytesToNatBE (bytes : ByteArray) : Nat := Id.run do
  let mut n := 0
  for byte in bytes.data do n := n * 256 + byte.toNat
  return n

private def natToBytesBE (n count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push ((n / 2 ^ (8 * (count - 1 - i)) % 256).toUInt8)
  return bytes

structure SecpSignature where
  r : Nat
  s : Nat
  recovery : Nat

def SecpSignature.canonicalRS (sig : SecpSignature) : ByteArray :=
  natToBytesBE sig.r 32 ++ natToBytesBE sig.s 32

def SecpSignature.bytes65 (sig : SecpSignature) : ByteArray :=
  -- viem's `sign` maps every nonzero recovery value to v = 28.
  sig.canonicalRS |>.push (if sig.recovery == 0 then 27 else 28)

/-- RFC 6979 deterministic ECDSA over a 32-byte digest, normalized to low-S. -/
def secp256k1SignDigest (privateKey digest : ByteArray) : Except String SecpSignature := do
  if privateKey.size != 32 || digest.size != 32 then
    throw "secp256k1 signing requires a 32-byte private key and digest"
  let d := bytesToNatBE privateKey
  if d == 0 || d >= secp256k1Order then throw "Invalid secp256k1 private key"
  let z := bytesToNatBE digest % secp256k1Order
  let seed := privateKey ++ natToBytesBE z 32
  let mut v := ByteArray.mk (Array.replicate 32 (1 : UInt8))
  let mut k := ByteArray.mk (Array.replicate 32 (0 : UInt8))
  k := hmacSHA256 k (v ++ (ByteArray.empty.push 0) ++ seed)
  v := hmacSHA256 k v
  k := hmacSHA256 k (v ++ (ByteArray.empty.push 1) ++ seed)
  v := hmacSHA256 k v
  for _ in [0:1000] do
    v := hmacSHA256 k v
    let nonce := bytesToNatBE v
    if nonce > 0 && nonce < secp256k1Order then
      let q := secp256k1BaseMul nonce
      let r := q.x % secp256k1Order
      if !q.infinity && r != 0 then
        let s := (inversePrime nonce secp256k1Order *
          ((z + r * d) % secp256k1Order)) % secp256k1Order
        if s != 0 then
          let lowS := if s > secp256k1Order / 2 then secp256k1Order - s else s
          let parity := q.y % 2
          let recovery := (if q.x >= secp256k1Order then 2 else 0) +
            (if lowS == s then parity else 1 - parity)
          return ⟨r, lowS, recovery⟩
    k := hmacSHA256 k (v.push 0)
    v := hmacSHA256 k v
  throw "RFC 6979 nonce generation exhausted 1000 candidates"

/-- Uncompressed 65-byte secp256k1 public key, 0x04 || x || y. -/
def secp256k1PublicKey (privateKey : ByteArray) : Except String ByteArray := do
  if privateKey.size != 32 then throw "secp256k1 private key must be 32 bytes"
  let scalar := bytesToNatBE privateKey
  if scalar == 0 || scalar >= secp256k1Order then throw "Invalid secp256k1 private key"
  let point := secp256k1BaseMul scalar
  return (ByteArray.empty.push 4) ++ natToBytesBE point.x 32 ++ natToBytesBE point.y 32

/-- Ethereum address: last 20 bytes of Keccak-256(uncompressed public key body). -/
def secp256k1EthereumAddress (privateKey : ByteArray) : Except String ByteArray := do
  let publicKey ← secp256k1PublicKey privateKey
  return (keccak256 (publicKey.extract 1 65)).extract 12 32

end LeanCrypto
