import Tornado.Crypto.Blake256

/-! Legacy BLAKE-256 vectors. Empty and `abc` are published examples; the
    boundary vectors were checked against pinned `@noble/hashes/blake1.js`
    used by `micro-zk-proofs` in the TypeScript CLI. -/

namespace Tornado.Crypto.Blake256Tests

private def rangeBytes (count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push (UInt8.ofNat (i % 256))
  return bytes

private def check (label : String) (bytes : ByteArray) (expected : String) : IO Unit := do
  let actual := blake256Hex bytes
  if actual != expected then
    throw <| IO.userError s!"{label}: got {actual}, expected {expected}"

def main : IO Unit := do
  check "empty" (rangeBytes 0)
    "716f6e863f744b9ac22c97ec7b76ea5f5908bc5b2f67c61510bfc4751384ea7a"
  check "abc" "abc".toUTF8
    "1833a9fa7cf4086bd5fda73da32e5a1d75b4c3f89d5c436369f9d78bb2da5c28"
  check "1" (rangeBytes 1)
    "0ce8d4ef4dd7cd8d62dfded9d4edb0a774ae6a41929a74da23109e8f11139c87"
  check "3" (rangeBytes 3)
    "d02f47c41931746796b435ca150e4192f0c961d8524220e7a675ae8a99280186"
  check "54" (rangeBytes 54)
    "6df0b232d9b4e86db83389705549c7f562b0700f7832d8a45062c7a87f550b59"
  check "55" (rangeBytes 55)
    "d7ec78bc615d99e41d371cf6401449969144b5f789bde014a9aeafd8987257f2"
  check "56" (rangeBytes 56)
    "26ca422697c9fabc642129b1a5669be07fb0a3c31f14f1c7859e048ad5958e44"
  check "63" (rangeBytes 63)
    "cfce445066d35322557b432540bd2f0af4caf9f426568236d9944426a5df792a"
  check "64" (rangeBytes 64)
    "4432b2c1e983b0c326583516920f3949c2acf5d85a99353601228cab40c867bc"
  check "65" (rangeBytes 65)
    "106cdd00dc14e257b1130d026b9fcc2c5ecbaae08fec13af0002ad6054c7bbd5"
  check "119" (rangeBytes 119)
    "7271691baf3f4ea7795006522897316eccd614816fa4fe10c546c11e882ac016"
  check "120" (rangeBytes 120)
    "6b4831d9c2ab2403b17ce7063f804ce559db6951563678294acd9a0a418bab35"
  check "127" (rangeBytes 127)
    "1446de0b1bc379c8b05fef5b9af281f322904af57c217351057cc955fd89d58a"
  check "128" (rangeBytes 128)
    "70a7b33d6d251c06757362fa717d0b19ceb0ebdccf48300a98156b5bb6b8c9a5"
  check "137" (rangeBytes 137)
    "8bd02eba72bedd572dc57e5f69b3a930b8269814a4f98cd5036cf72b267c4b58"
  check "4096" (rangeBytes 4096)
    "f1d29fe06f55e0976492c5129c32dfd08b92f7389f838096e1311433edf17e92"
  IO.println "BLAKE-256: 16 compatibility vectors passed"

end Tornado.Crypto.Blake256Tests

def main : IO Unit := Tornado.Crypto.Blake256Tests.main
