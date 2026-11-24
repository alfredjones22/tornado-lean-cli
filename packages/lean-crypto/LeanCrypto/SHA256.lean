import Lean

/-!
Pure Lean SHA-256 (FIPS 180-4) and HMAC-SHA256 (RFC 2104). These functions
use Lean's fixed-width `UInt32` and `ByteArray`; they do not call OpenSSL, a
subprocess, or C crypto bindings.
-/

namespace LeanCrypto

private def initialHash : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
  0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
  0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
  0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
  0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
  0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
]

private def rotr32 (word : UInt32) (bits : Nat) : UInt32 :=
  if bits % 32 == 0 then word
  else (word >>> UInt32.ofNat (bits % 32)) |||
    (word <<< UInt32.ofNat (32 - bits % 32))

private def smallSigma0 (x : UInt32) : UInt32 :=
  rotr32 x 7 ^^^ rotr32 x 18 ^^^ (x >>> 3)

private def smallSigma1 (x : UInt32) : UInt32 :=
  rotr32 x 17 ^^^ rotr32 x 19 ^^^ (x >>> 10)

private def bigSigma0 (x : UInt32) : UInt32 :=
  rotr32 x 2 ^^^ rotr32 x 13 ^^^ rotr32 x 22

private def bigSigma1 (x : UInt32) : UInt32 :=
  rotr32 x 6 ^^^ rotr32 x 11 ^^^ rotr32 x 25

private def pad (input : ByteArray) : ByteArray := Id.run do
  let mut bytes := input.push 0x80
  while bytes.size % 64 != 56 do
    bytes := bytes.push 0
  let bitLength := UInt64.ofNat (input.size * 8)
  for i in [0:8] do
    bytes := bytes.push (((bitLength >>> UInt64.ofNat (8 * (7 - i))).toNat % 256).toUInt8)
  return bytes

private def processBlock (hash : Array UInt32) (bytes : ByteArray) (block : Nat) : Array UInt32 := Id.run do
  let offset := block * 64
  let mut w : Array UInt32 := Array.replicate 64 0
  for i in [0:16] do
    let p := offset + 4 * i
    w := w.set! i ((bytes.get! p).toUInt32 <<< 24 |||
      (bytes.get! (p + 1)).toUInt32 <<< 16 |||
      (bytes.get! (p + 2)).toUInt32 <<< 8 |||
      (bytes.get! (p + 3)).toUInt32)
  for i in [16:64] do
    w := w.set! i (smallSigma1 w[i - 2]! + w[i - 7]! +
      smallSigma0 w[i - 15]! + w[i - 16]!)
  let mut a := hash[0]!
  let mut b := hash[1]!
  let mut c := hash[2]!
  let mut d := hash[3]!
  let mut e := hash[4]!
  let mut f := hash[5]!
  let mut g := hash[6]!
  let mut h := hash[7]!
  for i in [0:64] do
    let choose := (e &&& f) ^^^ ((~~~ e) &&& g)
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t1 := h + bigSigma1 e + choose + roundConstants[i]! + w[i]!
    let t2 := bigSigma0 a + majority
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  let mut output := hash
  for (word, index) in (#[a, b, c, d, e, f, g, h] : Array UInt32).toList.zipIdx do
    output := output.set! index (output[index]! + word)
  return output

/-- FIPS 180-4 SHA-256. For inputs of 2^64 or more bits, the length field
    wraps as specified by its 64-bit representation; normal CLI inputs are
    bounded far below that limit. -/
def sha256 (input : ByteArray) : ByteArray := Id.run do
  let padded := pad input
  let mut hash := initialHash
  for block in [0:padded.size / 64] do
    hash := processBlock hash padded block
  let mut digest := ByteArray.empty
  for word in hash do
    for i in [0:4] do
      digest := digest.push (((word >>> UInt32.ofNat (8 * (3 - i))).toNat % 256).toUInt8)
  return digest

/-- RFC 2104 HMAC-SHA256 with a 64-byte block key. -/
def hmacSHA256 (key message : ByteArray) : ByteArray := Id.run do
  let reduced := if key.size > 64 then sha256 key else key
  let mut innerKey := ByteArray.empty
  let mut outerKey := ByteArray.empty
  for i in [0:64] do
    let b := if i < reduced.size then reduced.get! i else 0
    innerKey := innerKey.push (b ^^^ (0x36 : UInt8))
    outerKey := outerKey.push (b ^^^ (0x5c : UInt8))
  return sha256 (outerKey ++ sha256 (innerKey ++ message))

private def hexOfBytes (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for byte in bytes.data do
    let n := byte.toNat
    out := out.push digits[n / 16]!
    out := out.push digits[n % 16]!
  return out

def sha256Hex (input : ByteArray) : String := hexOfBytes (sha256 input)

def hmacSHA256Hex (key message : ByteArray) : String :=
  hexOfBytes (hmacSHA256 key message)

end LeanCrypto
