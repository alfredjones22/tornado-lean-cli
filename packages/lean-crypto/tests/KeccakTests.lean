import LeanCrypto.Keccak

/-!
Deterministic compatibility vectors for Ethereum Keccak-256. The empty and
`abc` digests are standard public Keccak examples. The byte-range cases were
cross-checked against the pinned CLI's `viem` implementation and exercise both
sides of the 136-byte rate boundary.

Run with `lake env lean --run Tornado/Crypto/KeccakTests.lean` after building
the Keccak module.
-/

namespace LeanCrypto.KeccakTests

private def rangeBytes (count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push (UInt8.ofNat (i % 256))
  return bytes

private def check (name : String) (input : ByteArray) (expected : String) : IO Unit := do
  let actual := keccak256Hex input
  if actual != expected then
    throw <| IO.userError s!"{name}: got {actual}, expected {expected}"

def main : IO Unit := do
  check "empty" (rangeBytes 0)
    "0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
  check "abc" "abc".toUTF8
    "0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
  check "one byte" (rangeBytes 1)
    "0xbc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"
  check "three bytes" (rangeBytes 3)
    "0xf84a97f1f0a956e738abd85c2e0a5026f8874e3ec09c8f012159dfeeaab2b156"
  check "rate minus one" (rangeBytes 135)
    "0xcbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62"
  check "exact rate" (rangeBytes 136)
    "0x7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e"
  check "rate plus one" (rangeBytes 137)
    "0xac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db"
  check "two rates" (rangeBytes 272)
    "0xfdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e"
  check "two rates minus one" (rangeBytes 271)
    "0x7c974895b2a88303ff2dc6b58f438ceb0b298cac91099ac0539cc0f477506191"
  check "two rates plus one" (rangeBytes 273)
    "0x4f707289a9c3ccd0c4a51f2f17339f5dd171d371c04ff7783b735b5b22682eaf"
  check "large payload" (rangeBytes 4096)
    "0x1c85a3e5666494583f321cd54285cc17276acf9aea34b207d43005bfa69d0a86"
  IO.println "Keccak-256: 11 compatibility vectors passed"

end LeanCrypto.KeccakTests

def main : IO Unit := LeanCrypto.KeccakTests.main
