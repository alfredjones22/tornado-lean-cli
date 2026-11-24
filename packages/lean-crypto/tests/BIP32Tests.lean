import LeanCrypto.BIP32
import LeanCrypto.BIP39

namespace LeanCrypto.BIP32Tests

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
  let mnemonic :=
    "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon art"
  let seed ← unwrap "BIP39 seed" (mnemonicToSeedEnglish mnemonic)
  let master ← unwrap "BIP32 master" (bip32MasterFromSeed seed)
  check "master private key" (hexBytes master.privateKey)
    "235b34cd7c9f6d7e4595ffe9ae4b1cb5606df8aca2b527d20a07c8f56b2342f4"
  check "master chain code" (hexBytes master.chainCode)
    "f40eaad21641ca7cb5ac00f9ce21cac9ba070bb673a237f7bce57acda54386a4"
  let coin ← unwrap "m/29795'" (bip32HardenedChild master 29795)
  check "m/29795' key" (hexBytes coin.privateKey)
    "91bec03ebf75230202415aae63a3804ba77369646c696a8d180d17ccab9c6de7"
  check "m/29795' chain" (hexBytes coin.chainCode)
    "4576cec0adfdf823a2eb0b405c56da7fb6cbf92c4fc091dfa362566cd9fc1ad1"
  let scheme ← unwrap "m/29795'/1'" (bip32HardenedChild coin 1)
  check "m/29795'/1' key" (hexBytes scheme.privateKey)
    "e93f479a89c70e1d233162e059a1c4ed5ccec3141728d3ffc5d726df0c7db77b"
  check "m/29795'/1' chain" (hexBytes scheme.chainCode)
    "af17fbfb7148a3dca1fa00b8e87e4977eaff71e7232312243594181d2f538353"
  let signer ← unwrap "m/29795'/1'/0'" (bip32HardenedChild scheme 0)
  check "Tornado signer private key" (hexBytes signer.privateKey)
    "a0030e1f064deb82242c2915d0ec910c23656641e72904c10055c5e395bad5bb"
  check "Tornado signer chain" (hexBytes signer.chainCode)
    "cf2a36cfe4fc82036adc1a253b8d073c09137ced93636fae45a1c7c707b4629d"
  if (bip32HardenedChild master 0x80000000).isOk then
    throw <| IO.userError "Out-of-range hardened index accepted"
  if (bip32MasterFromSeed ByteArray.empty).isOk then
    throw <| IO.userError "Empty BIP32 master seed accepted"
  IO.println "BIP32 Tornado signing path: 10 compatibility and rejection checks passed"

end LeanCrypto.BIP32Tests

def main : IO Unit := LeanCrypto.BIP32Tests.main
