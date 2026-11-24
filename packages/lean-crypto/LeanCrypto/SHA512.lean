import Lean

/-!
Pure Lean SHA-512 and HMAC-SHA512. SHA-512 is used by BIP39 and BIP32 when
turning a Tornado recovery phrase into the deterministic note signing key.
There are no external crypto bindings or subprocesses in this module.
-/

namespace LeanCrypto

private def initialHash512 : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
  0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f,
  0x1f83d9abfb41bd6b, 0x5be0cd19137e2179
]

private def roundConstants512 : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
]

private def rotr64 (word : UInt64) (bits : Nat) : UInt64 :=
  if bits % 64 == 0 then word
  else (word >>> UInt64.ofNat (bits % 64)) |||
    (word <<< UInt64.ofNat (64 - bits % 64))

private def smallSigma0_512 (x : UInt64) : UInt64 :=
  rotr64 x 1 ^^^ rotr64 x 8 ^^^ (x >>> 7)

private def smallSigma1_512 (x : UInt64) : UInt64 :=
  rotr64 x 19 ^^^ rotr64 x 61 ^^^ (x >>> 6)

private def bigSigma0_512 (x : UInt64) : UInt64 :=
  rotr64 x 28 ^^^ rotr64 x 34 ^^^ rotr64 x 39

private def bigSigma1_512 (x : UInt64) : UInt64 :=
  rotr64 x 14 ^^^ rotr64 x 18 ^^^ rotr64 x 41

private def pad512 (input : ByteArray) : ByteArray := Id.run do
  let mut bytes := input.push 0x80
  while bytes.size % 128 != 112 do
    bytes := bytes.push 0
  let bitLength := input.size * 8
  for i in [0:16] do
    bytes := bytes.push ((bitLength / 2 ^ (8 * (15 - i)) % 256).toUInt8)
  return bytes

private def processBlock512 (hash : Array UInt64) (bytes : ByteArray) (block : Nat) : Array UInt64 := Id.run do
  let offset := block * 128
  let mut w : Array UInt64 := Array.replicate 80 0
  for i in [0:16] do
    let p := offset + 8 * i
    let mut word : UInt64 := 0
    for j in [0:8] do
      word := (word <<< 8) ||| (bytes.get! (p + j)).toUInt64
    w := w.set! i word
  for i in [16:80] do
    w := w.set! i (smallSigma1_512 w[i - 2]! + w[i - 7]! +
      smallSigma0_512 w[i - 15]! + w[i - 16]!)
  let mut a := hash[0]!
  let mut b := hash[1]!
  let mut c := hash[2]!
  let mut d := hash[3]!
  let mut e := hash[4]!
  let mut f := hash[5]!
  let mut g := hash[6]!
  let mut h := hash[7]!
  for i in [0:80] do
    let choose := (e &&& f) ^^^ ((~~~ e) &&& g)
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t1 := h + bigSigma1_512 e + choose + roundConstants512[i]! + w[i]!
    let t2 := bigSigma0_512 a + majority
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  let mut output := hash
  for (word, index) in (#[a, b, c, d, e, f, g, h] : Array UInt64).toList.zipIdx do
    output := output.set! index (output[index]! + word)
  return output

/-- FIPS 180-4 SHA-512. -/
def sha512 (input : ByteArray) : ByteArray := Id.run do
  let padded := pad512 input
  let mut hash := initialHash512
  for block in [0:padded.size / 128] do
    hash := processBlock512 hash padded block
  let mut digest := ByteArray.empty
  for word in hash do
    for i in [0:8] do
      digest := digest.push (((word >>> UInt64.ofNat (8 * (7 - i))).toNat % 256).toUInt8)
  return digest

/-- RFC 2104 HMAC-SHA512 with a 128-byte block key. -/
def hmacSHA512 (key message : ByteArray) : ByteArray := Id.run do
  let reduced := if key.size > 128 then sha512 key else key
  let mut innerKey := ByteArray.empty
  let mut outerKey := ByteArray.empty
  for i in [0:128] do
    let b := if i < reduced.size then reduced.get! i else 0
    innerKey := innerKey.push (b ^^^ (0x36 : UInt8))
    outerKey := outerKey.push (b ^^^ (0x5c : UInt8))
  return sha512 (outerKey ++ sha512 (innerKey ++ message))

private def hexOfBytes512 (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for byte in bytes.data do
    let n := byte.toNat
    out := out.push digits[n / 16]!
    out := out.push digits[n % 16]!
  return out

def sha512Hex (input : ByteArray) : String := hexOfBytes512 (sha512 input)

def hmacSHA512Hex (key message : ByteArray) : String :=
  hexOfBytes512 (hmacSHA512 key message)

end LeanCrypto
