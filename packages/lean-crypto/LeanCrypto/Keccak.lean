import Lean

/-!
Ethereum Keccak-256, implemented in Lean. This is Keccak's original `pad10*1`
domain (`0x01`), not NIST SHA3-256 (`0x06`). The sponge has a 1088-bit rate
and a 512-bit capacity. Lanes are little-endian as in Keccak-f[1600].

The implementation is pure: no C FFI, subprocess, or crypto library. `UInt64`
arithmetic and `ByteArray` come from Lean's runtime.
-/

namespace LeanCrypto

private def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
  0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
  0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
  0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
  0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
  0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
  0x8000000000008080, 0x0000000080000001, 0x8000000080008008
]

-- Indexed by x + 5*y.
private def rhoOffsets : Array Nat := #[
   0,  1, 62, 28, 27,
  36, 44,  6, 55, 20,
   3, 10, 43, 25, 39,
  41, 45, 15, 21,  8,
  18,  2, 61, 56, 14
]

private def rotl64 (word : UInt64) (bits : Nat) : UInt64 :=
  if bits % 64 == 0 then word
  else (word <<< UInt64.ofNat (bits % 64)) |||
    (word >>> UInt64.ofNat (64 - bits % 64))

private def keccakRound (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  let mut c : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    c := c.set! x (a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^
      a[x + 15]! ^^^ a[x + 20]!)
  let mut d : Array UInt64 := Array.replicate 5 0
  for x in [0:5] do
    d := d.set! x (c[(x + 4) % 5]! ^^^ rotl64 c[(x + 1) % 5]! 1)
  let mut theta := a
  for x in [0:5] do
    for y in [0:5] do
      let i := x + 5 * y
      theta := theta.set! i (theta[i]! ^^^ d[x]!)
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      let i := x + 5 * y
      let j := y + 5 * ((2 * x + 3 * y) % 5)
      b := b.set! j (rotl64 theta[i]! rhoOffsets[i]!)
  let mut out := b
  for x in [0:5] do
    for y in [0:5] do
      let i := x + 5 * y
      out := out.set! i (b[i]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&&
        b[(x + 2) % 5 + 5 * y]!))
  return out.set! 0 (out[0]! ^^^ rc)

/-- Keccak-f[1600] permutation on 25 little-endian 64-bit lanes. -/
def keccakF1600 (state : Array UInt64) : Array UInt64 := Id.run do
  let mut a := state
  for rc in roundConstants do
    a := keccakRound a rc
  return a

private def absorbBlock (state : Array UInt64) (input : ByteArray)
    (block : Nat) (last : Bool) : Array UInt64 := Id.run do
  let mut a := state
  for i in [0:136] do
    let position := block * 136 + i
    let payload : UInt8 :=
      if position < input.size then input.get! position
      else if position == input.size then 0x01
      else 0
    let byte := if last && i == 135 then payload ^^^ (0x80 : UInt8) else payload
    let lane := i / 8
    let shift := UInt64.ofNat (8 * (i % 8))
    a := a.set! lane (a[lane]! ^^^ (byte.toUInt64 <<< shift))
  return keccakF1600 a

/-- Ethereum Keccak-256 of arbitrary bytes. The returned 32 bytes are the
    first 256 sponge bits, serialized little-endian within each 64-bit lane. -/
def keccak256 (input : ByteArray) : ByteArray := Id.run do
  let mut state : Array UInt64 := Array.replicate 25 0
  let blocks := input.size / 136 + 1
  for block in [0:blocks] do
    state := absorbBlock state input block (block + 1 == blocks)
  let mut digest := ByteArray.empty
  for i in [0:32] do
    let lane := state[i / 8]!
    let byte := ((lane >>> UInt64.ofNat (8 * (i % 8))).toNat % 256).toUInt8
    digest := digest.push byte
  return digest

/-- Lowercase hexadecimal, without a `0x` prefix. -/
def bytesToHex (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut out := ""
  for byte in bytes.data do
    let n := byte.toNat
    out := out.push digits[n / 16]!
    out := out.push digits[n % 16]!
  return out

/-- Ethereum Keccak-256 as a `0x`-prefixed hexadecimal string. -/
def keccak256Hex (input : ByteArray) : String :=
  "0x" ++ bytesToHex (keccak256 input)

end LeanCrypto
