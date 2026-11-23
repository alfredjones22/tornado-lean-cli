import Tornado.Crypto.TornadoSignature

namespace Tornado.Crypto.TornadoSignatureTests

private def bigEndian (n count : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:count] do
    result := result.push ((n / 2 ^ (8 * (count - 1 - i)) % 256).toUInt8)
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
  let key := bigEndian 0xa0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb 32
  check "mainnet nonce 0 EIP-712 hash"
    (hexBytes (← unwrap "EIP-712 hash" (tornadoNoteTypedDataHash 1 0)))
    "0689bc25b1186d35225f153ccbefbae815389ab73160fe51a84a8b2c407ec3f7"
  check "mainnet nonce 1 EIP-712 hash"
    (hexBytes (← unwrap "EIP-712 hash" (tornadoNoteTypedDataHash 1 1)))
    "b1a69ccc0091b72e1944ed6463b319a6c805a9e3c2558dcd181c0284124e50f5"
  check "Sepolia nonce 0 EIP-712 hash"
    (hexBytes (← unwrap "EIP-712 hash" (tornadoNoteTypedDataHash 11155111 0)))
    "2cd3f95987a0f30a822969e1a0bdb895fc397940809327bc260ca67e58cffb6f"
  let sig0 ← unwrap "mainnet signature" (tornadoNoteSignature key 1 0)
  check "mainnet nonce 0 canonical signature" (hexBytes sig0.canonicalRS)
    "5cffc4e8637258b6dd73611f2809c7a771082d307af085bf10f159344016dbb02a8f84847602c131741ecc7495a9aa50e9c69120c7fe8936ee70a62ae022d7e0"
  let sig1 ← unwrap "Sepolia signature" (tornadoNoteSignature key 11155111 0)
  check "Sepolia nonce 0 canonical signature" (hexBytes sig1.canonicalRS)
    "34b62185a7e67934437082a62b6aed9bce22264c7c7f3bcddaf34f246862f0c122fcb860f8ca045fb57e2c7d4e49e6fbbac543bea9c9260a3b962a5f1077b0a7"
  let note0 ← unwrap "mainnet note 0" (tornadoSignatureNote key 1 0 0x199112eb461ea7eec1d75b33343542e1d069b41c)
  check "mainnet note 0 preimage" (hexBytes note0.preimage)
    "33567fb6463d588b0ef7ff2d415130e0d91059781005f504671ddc3f03c4adc8b873cfa627a16e46d1f33b81d9c7e86772a083575ccccb9104ed77057b53"
  check "mainnet note 0 commitment" (hexBytes (bigEndian note0.commitment 32))
    "2b0157e9206b3a9fc60465b9412e1390f1dcc02719231b30c6543ed273639600"
  check "mainnet note 0 nullifier hash" (hexBytes (bigEndian note0.nullifierHash 32))
    "205b9f8c18eaa3b4827ac12f3898fb5b90d3a28de7e95ddda4e428a52556c9b8"
  let note1 ← unwrap "mainnet note 1" (tornadoSignatureNote key 1 1 0x47ce0c6ed5b0ce3d3a51fdb1c52dc66a7c3c2936)
  check "mainnet note 1 preimage" (hexBytes note1.preimage)
    "38ba0d601404fd62799e1f48f412425062db944406ad748338cdf17cc91e1b0e52370aca05d3731e2f6e278d0fb871ecedf5a9de9a20969a636b16acde90"
  check "mainnet note 1 commitment" (hexBytes (bigEndian note1.commitment 32))
    "270b17f82575e4a5fb331e445c8f316d6b335ad47a19c631c814cd99ba5e008b"
  check "mainnet note 1 nullifier hash" (hexBytes (bigEndian note1.nullifierHash 32))
    "11b6247391a5bb391f49af6544451f7f70bc8fcf48cf655b49b7549ad2a50603"
  if (tornadoNoteTypedDataHash 1 (2 ^ 64)).isOk then
    throw <| IO.userError "Out-of-range nonce accepted"
  if (tornadoSignatureNote key 1 0 (2 ^ 160)).isOk then
    throw <| IO.userError "Out-of-range pool address accepted"
  IO.println "Tornado EIP-712 seeded notes: 13 pinned SDK/viem compatibility checks passed"

end Tornado.Crypto.TornadoSignatureTests

def main : IO Unit := Tornado.Crypto.TornadoSignatureTests.main
