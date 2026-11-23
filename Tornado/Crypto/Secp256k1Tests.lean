import Tornado.Crypto.Secp256k1

namespace Tornado.Crypto.Secp256k1Tests

private def bigEndian (n count : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:count] do
    result := result.push ((n / 2 ^ (8 * (count - 1 - i)) % 256).toUInt8)
  return result

private def fill (n : Nat) (b : UInt8) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for _ in [0:n] do result := result.push b
  return result

private def hexBytes (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut result := ""
  for byte in bytes.data do
    result := result.push digits[byte.toNat / 16]!
    result := result.push digits[byte.toNat % 16]!
  return result

private def check (label actual expected : String) : IO Unit :=
  if actual == expected then pure ()
  else throw <| IO.userError s!"{label}: got {actual}, expected {expected}"

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"{label}: {e}"

def main : IO Unit := do
  let g := secp256k1BaseMul 1
  check "generator x" (toString g.x)
    (toString (0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798 : Nat))
  check "generator y" (toString g.y)
    (toString (0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8 : Nat))
  if !(secp256k1BaseMul secp256k1Order).infinity then
    throw <| IO.userError "Group-order scalar did not map to infinity"
  let key := bigEndian 0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb 32
  let address ← unwrap "Ethereum address" (secp256k1EthereumAddress key)
  check "Ethereum address" (hexBytes address) "6f16147af0b7c30369b96f817af55e30baa425ac"
  let zeroSig ← unwrap "zero digest signature" (secp256k1SignDigest key (fill 32 0))
  check "zero digest signature" (hexBytes zeroSig.canonicalRS)
    "48a67584d0808f4587148247d9fa1d69714df2703b7c4bdab6aad9ea7480bf6d3a4c6a289a5915d7a0bbee1a0286dd99edcb819e55779e77e12ca48424a3bc2c"
  check "zero digest recovery" (toString zeroSig.recovery) "0"
  check "zero digest viem signature" (hexBytes zeroSig.bytes65)
    "48a67584d0808f4587148247d9fa1d69714df2703b7c4bdab6aad9ea7480bf6d3a4c6a289a5915d7a0bbee1a0286dd99edcb819e55779e77e12ca48424a3bc2c1b"
  let oneSig ← unwrap "one digest signature" (secp256k1SignDigest key (fill 32 1))
  check "one digest signature" (hexBytes oneSig.canonicalRS)
    "ed21d55b55f3a6c96565b9d8ea0cb3d7a618f3c4264f9fc59bddb3017e1e3751196be08ff13cb1d8d04520864ed0463a48285adbda60411fdc09e42785c280e7"
  check "one digest recovery" (toString oneSig.recovery) "1"
  check "one digest viem signature" (hexBytes oneSig.bytes65)
    "ed21d55b55f3a6c96565b9d8ea0cb3d7a618f3c4264f9fc59bddb3017e1e3751196be08ff13cb1d8d04520864ed0463a48285adbda60411fdc09e42785c280e71c"
  if (secp256k1SignDigest (fill 32 0) (fill 32 0)).isOk then
    throw <| IO.userError "Zero private key accepted"
  IO.println "secp256k1 deterministic signatures: 11 compatibility and rejection checks passed"

end Tornado.Crypto.Secp256k1Tests

def main : IO Unit := Tornado.Crypto.Secp256k1Tests.main
