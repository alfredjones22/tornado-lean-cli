import Tornado.Crypto.SHA512

/-! SHA-512 and HMAC-SHA512 parity vectors from Node crypto; empty, abc and
RFC 4231 #1 also have published standard expected values. -/

namespace Tornado.Crypto.SHA512Tests

private def rangeBytes (count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push (UInt8.ofNat (i % 256))
  return bytes

private def repeatedByte (count : Nat) (byte : UInt8) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for _ in [0:count] do
    bytes := bytes.push byte
  return bytes

private def check (label actual expected : String) : IO Unit :=
  if actual == expected then pure ()
  else throw <| IO.userError s!"{label}: got {actual}, expected {expected}"

def main : IO Unit := do
  check "sha512 empty" (sha512Hex (rangeBytes 0))
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
  check "sha512 abc" (sha512Hex "abc".toUTF8)
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
  check "sha512 111" (sha512Hex (rangeBytes 111))
    "a1a111449b198d9b1f538bad7f3fc1022b3a5b1a5e90a0bc860de8512746cbc31599e6c834de3a3235327af0b51ff57bf7acf1974a73014d9c3953812edc7c8d"
  check "sha512 112" (sha512Hex (rangeBytes 112))
    "c5fbd731d19d2ae1180f001be72c2c1aaba1d7b094b3748880e24593b8e117a750e11c1bd867cc2f96dace8c8b74abd2d5c4f236be444e77d30d1916174070b9"
  check "sha512 127" (sha512Hex (rangeBytes 127))
    "eab89674feaa34e27aebeeff3c0a4d70070bb872d5e9f186cf1dbbdee517b6e35724d629ff025a5b07185e911ada7e3c8acf830aa0e4f71777bd2d44f504f7f0"
  check "sha512 128" (sha512Hex (rangeBytes 128))
    "1dffd5e3adb71d45d2245939665521ae001a317a03720a45732ba1900ca3b8351fc5c9b4ca513eba6f80bc7b1d1fdad4abd13491cb824d61b08d8c0e1561b3f7"
  check "sha512 129" (sha512Hex (rangeBytes 129))
    "1d9da57fbbdab09afb3506ab2d223d06109d65c1c8ad197f50138f714bc4c3f2fe5787922639c680acad1c651f955990425954ce2cba0c5cc83f2667d878eb0f"
  check "sha512 4096" (sha512Hex (rangeBytes 4096))
    "034a1bd3ad5dbddf6c9aed6b1705661487e110dc7e158fe330c94363e8ffb53b1c92f883010fd73ce8a86115b7b4712ba0f3a9279760ed6220a5773eb54425f0"
  check "hmac RFC 4231 #1"
    (hmacSHA512Hex (repeatedByte 20 0x0b) "Hi There".toUTF8)
    "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854"
  check "hmac empty key" (hmacSHA512Hex (repeatedByte 0 0xaa) "message".toUTF8)
    "08fce52f6395d59c2a3fb8abb281d74ad6f112b9a9c787bcea290d94dadbc82b2ca3e5e12bf2277c7fedbb0154d5493e41bb7459f63c8e39554ea3651b812492"
  check "hmac 20-byte key" (hmacSHA512Hex (repeatedByte 20 0xaa) "message".toUTF8)
    "442abb041bbc3a7f2b90219a54a4708863aa07665dcb316cab8599303a8a3e453193e8f15b8c0b266f715babe4cfcc1e1ea4923f63b1121ec1d7734111c631b8"
  check "hmac 128-byte key" (hmacSHA512Hex (repeatedByte 128 0xaa) "message".toUTF8)
    "d726b7cbe87eec6ddc160756e39d20d73650896bc8ea082d985c10c052649385f79c69249e31790b306673774fc9803496028f9eb47c789b43e411eaca3b2570"
  check "hmac 129-byte key" (hmacSHA512Hex (repeatedByte 129 0xaa) "message".toUTF8)
    "3969b40bd770aa435c6e2d5dbcc5afd9b4a32e876a7de5931e9c1eb9d3c1debc9d08056ce9b439b4aeb74e7d66f28ebe46473c0088dfbb63efba331d86422470"
  check "hmac 131-byte key" (hmacSHA512Hex (repeatedByte 131 0xaa) "message".toUTF8)
    "ec4f1df2b034b892650c5e109e504dffc18791347724ed99278e7dc8d4d10f90bc96728a8620608b98124240e3eebeff6e2b73f6034ee9acd11ac84d2b3c191c"
  IO.println "SHA-512/HMAC-SHA512: 14 compatibility vectors passed"

end Tornado.Crypto.SHA512Tests

def main : IO Unit := Tornado.Crypto.SHA512Tests.main
