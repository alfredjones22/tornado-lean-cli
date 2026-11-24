import Lean

/-!
Legacy BLAKE-256 (the BLAKE SHA-3 candidate), as used by
`micro-zk-proofs/pedersen.js` to derive BabyJubJub generator points. This is
not BLAKE2s or BLAKE3. It is the unsalted 14-round variant with a 64-byte
block and the original BLAKE-256 finalization flags.

The implementation is pure Lean and has no crypto FFI.
-/

namespace LeanCrypto

private def iv : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
]

private def constants : Array UInt32 := #[
  0x243f6a88, 0x85a308d3, 0x13198a2e, 0x03707344,
  0xa4093822, 0x299f31d0, 0x082efa98, 0xec4e6c89,
  0x452821e6, 0x38d01377, 0xbe5466cf, 0x34e90c6c,
  0xc0ac29b7, 0xc97c50dd, 0x3f84d5b5, 0xb5470917
]

-- Blake's ten-row sigma schedule. Rounds 10..13 repeat rows 0..3.
private def sigma : Array (Array Nat) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]
]

private def rotr32 (word : UInt32) (bits : Nat) : UInt32 :=
  if bits % 32 == 0 then word
  else (word >>> UInt32.ofNat (bits % 32)) |||
    (word <<< UInt32.ofNat (32 - bits % 32))

private def mix (v : Array UInt32) (a b c d : Nat) (x y : UInt32) : Array UInt32 := Id.run do
  let mut va := v[a]!
  let mut vb := v[b]!
  let mut vc := v[c]!
  let mut vd := v[d]!
  va := va + vb + x
  vd := rotr32 (vd ^^^ va) 16
  vc := vc + vd
  vb := rotr32 (vb ^^^ vc) 12
  va := va + vb + y
  vd := rotr32 (vd ^^^ va) 8
  vc := vc + vd
  vb := rotr32 (vb ^^^ vc) 7
  return (((v.set! a va).set! b vb).set! c vc).set! d vd

private def compress (hash : Array UInt32) (block : ByteArray)
    (counterBits : UInt64) (withLength : Bool) : Array UInt32 := Id.run do
  let mut m : Array UInt32 := Array.replicate 16 0
  for i in [0:16] do
    let p := 4 * i
    m := m.set! i ((block.get! p).toUInt32 <<< 24 |||
      (block.get! (p + 1)).toUInt32 <<< 16 |||
      (block.get! (p + 2)).toUInt32 <<< 8 |||
      (block.get! (p + 3)).toUInt32)
  let mut v : Array UInt32 := Array.replicate 16 0
  for i in [0:8] do
    v := v.set! i hash[i]!
    v := v.set! (i + 8) constants[i]!
  if withLength then
    let lo := UInt32.ofNat (counterBits.toNat % 0x100000000)
    let hi := UInt32.ofNat (counterBits.toNat / 0x100000000)
    v := v.set! 12 (v[12]! ^^^ lo)
    v := v.set! 13 (v[13]! ^^^ lo)
    v := v.set! 14 (v[14]! ^^^ hi)
    v := v.set! 15 (v[15]! ^^^ hi)
  for round in [0:14] do
    let s := sigma[round % 10]!
    -- Column G functions, then diagonal G functions.
    for i in [0:8] do
      let j := 2 * i
      let sx := s[j]!
      let sy := s[j + 1]!
      let x := m[sx]! ^^^ constants[sy]!
      let y := m[sy]! ^^^ constants[sx]!
      let (a, b, c, d) :=
        if i < 4 then (i, i + 4, i + 8, i + 12)
        else
          match i - 4 with
          | 0 => (0, 5, 10, 15)
          | 1 => (1, 6, 11, 12)
          | 2 => (2, 7, 8, 13)
          | _ => (3, 4, 9, 14)
      v := mix v a b c d x y
  let mut out := hash
  for i in [0:8] do
    out := out.set! i (hash[i]! ^^^ v[i]! ^^^ v[i + 8]!)
  return out

private def paddedBlock (input : ByteArray) (offset count : Nat) : ByteArray := Id.run do
  let mut block := ByteArray.empty
  for i in [0:count] do
    block := block.push (input.get! (offset + i))
  block := block.push 0x80
  while block.size < 64 do
    block := block.push 0
  return block

private def withLengthAndFlag (block : ByteArray) (bitLength : UInt64) : ByteArray := Id.run do
  let mut b := block.set! 55 (block.get! 55 ||| (0x01 : UInt8))
  for i in [0:8] do
    b := b.set! (56 + i)
      (((bitLength >>> UInt64.ofNat (8 * (7 - i))).toNat % 256).toUInt8)
  return b

/-- Unsalted legacy BLAKE-256. This is the exact variant used to generate
    Pedersen bases in the pinned `micro-zk-proofs` dependency. -/
def blake256 (input : ByteArray) : ByteArray := Id.run do
  let full := input.size / 64
  let rem := input.size % 64
  let bitLength := UInt64.ofNat (input.size * 8)
  let mut hash := iv
  for block in [0:full] do
    let bytes := input.extract (block * 64) ((block + 1) * 64)
    hash := compress hash bytes (UInt64.ofNat ((block + 1) * 512)) true
  let padded := paddedBlock input (full * 64) rem
  if rem > 55 then
    hash := compress hash padded bitLength true
    let final := withLengthAndFlag (ByteArray.mk (Array.replicate 64 0)) bitLength
    hash := compress hash final 0 false
  else
    let final := withLengthAndFlag padded bitLength
    hash := compress hash final bitLength (rem != 0)
  let mut digest := ByteArray.empty
  for word in hash do
    for i in [0:4] do
      digest := digest.push (((word >>> UInt32.ofNat (8 * (3 - i))).toNat % 256).toUInt8)
  return digest

/-- Lowercase hexadecimal BLAKE-256 digest, without `0x`. -/
def blake256Hex (input : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for byte in (blake256 input).data do
    let n := byte.toNat
    out := out.push digits[n / 16]!
    out := out.push digits[n % 16]!
  return out

end LeanCrypto
