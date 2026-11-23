import Tornado.Crypto.BIP39

namespace Tornado.Crypto.BIP39Tests

private def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for _ in [0:n] do bytes := bytes.push 0
  return bytes

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
  check "English wordlist length" (toString bip39EnglishWords.size) "2048"
  check "English wordlist first" bip39EnglishWords[0]! "abandon"
  check "English wordlist last" bip39EnglishWords[2047]! "zoo"
  let words24 ← unwrap "24-word generation" (entropyToMnemonicEnglish (zeroBytes 32))
  check "zero entropy 24 words" words24
    "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon art"
  check "zero entropy 24-word inverse"
    (hexBytes (← unwrap "24-word inverse" (mnemonicToEntropyEnglish words24)))
    (hexBytes (zeroBytes 32))
  let words12 ← unwrap "12-word generation" (entropyToMnemonicEnglish (zeroBytes 16))
  check "zero entropy 12 words" words12
    "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about"
  check "zero entropy 12-word inverse"
    (hexBytes (← unwrap "12-word inverse" (mnemonicToEntropyEnglish words12)))
    (hexBytes (zeroBytes 16))
  check "24-word BIP39 seed"
    (hexBytes (← unwrap "24-word seed" (mnemonicToSeedEnglish words24)))
    "408b285c123836004f4b8842c89324c1f01382450c0d439af345ba7fc49acf705489c6fc77dbd4e3dc1dd8cc6bc9f043db8ada1e243c4a0eafb290d399480840"
  check "12-word TREZOR BIP39 seed"
    (hexBytes (← unwrap "TREZOR seed" (mnemonicToSeedEnglish words12 "TREZOR")))
    "c55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04"
  if (mnemonicToEntropyEnglish (words12 ++ " about")).isOk then
    throw <| IO.userError "Invalid word count accepted"
  if (mnemonicToEntropyEnglish ("zoo" ++ (words12.drop 7).toString)).isOk then
    throw <| IO.userError "Invalid mnemonic accepted"
  let privateWord := "privateword"
  let invalidPhrase := String.intercalate " " (privateWord :: (words12.splitOn " ").drop 1)
  match mnemonicToEntropyEnglish invalidPhrase with
  | .ok _ => throw <| IO.userError "Unknown mnemonic word accepted"
  | .error message =>
    if message.contains privateWord then
      throw <| IO.userError "Mnemonic parser echoed private input"
  if (mnemonicToSeedEnglish words12 "é").isOk then
    throw <| IO.userError "Unicode passphrase accepted without NFKD"
  IO.println "BIP39 English: 12 compatibility and rejection checks passed"

end Tornado.Crypto.BIP39Tests

def main : IO Unit := Tornado.Crypto.BIP39Tests.main
