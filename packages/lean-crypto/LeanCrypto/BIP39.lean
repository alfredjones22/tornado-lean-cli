import LeanCrypto.SHA256
import LeanCrypto.SHA512
import LeanCrypto.BIP39Words

/-!
The English BIP39 route used by the Tornado CLI. Mnemonics are validated for
word count, vocabulary, and checksum before deriving a seed. The CLI supplies
no passphrase; non-ASCII passphrases are rejected because Lean core has no NFKD
normalizer and silently accepting one could derive a different recovery key.
-/

namespace LeanCrypto

private def validEntropyLength (length : Nat) : Bool :=
  length == 16 || length == 20 || length == 24 || length == 28 || length == 32

private def validWordCount (count : Nat) : Bool :=
  count == 12 || count == 15 || count == 18 || count == 21 || count == 24

private def entropyBit (entropy : ByteArray) (checksum : UInt8) (position : Nat) : Nat :=
  if position < entropy.size * 8 then
    ((entropy.get! (position / 8)).toNat / 2 ^ (7 - position % 8)) % 2
  else
    (checksum.toNat / 2 ^ (7 - (position - entropy.size * 8))) % 2

/-- Convert 128..256 bits of entropy to the specified English BIP39 phrase. -/
def entropyToMnemonicEnglish (entropy : ByteArray) : Except String String := do
  if !validEntropyLength entropy.size then
    throw "BIP39 English entropy must be 16, 20, 24, 28, or 32 bytes"
  let checksum := (sha256 entropy).get! 0
  let count := entropy.size * 3 / 4
  let mut words : Array String := #[]
  for i in [0:count] do
    let mut index := 0
    for j in [0:11] do
      index := index * 2 + entropyBit entropy checksum (i * 11 + j)
    words := words.push bip39EnglishWords[index]!
  return String.intercalate " " words.toList

private def englishWordIndex (word : String) : Option Nat := Id.run do
  for i in [0:bip39EnglishWords.size] do
    if bip39EnglishWords[i]! == word then return some i
  return none

/-- Validate an English BIP39 phrase and return its original entropy. -/
def mnemonicToEntropyEnglish (mnemonic : String) : Except String ByteArray := do
  let words := mnemonic.splitOn " "
  if !validWordCount words.length then
    throw "BIP39 English mnemonic must contain 12, 15, 18, 21, or 24 words"
  let mut bits : Array Nat := #[]
  for word in words do
    let some index := englishWordIndex word
      | throw "Unknown BIP39 English word"
    for j in [0:11] do
      bits := bits.push ((index / 2 ^ (10 - j)) % 2)
  let entropyLength := words.length * 4 / 3
  let mut entropy := ByteArray.empty
  for i in [0:entropyLength] do
    let mut byte := 0
    for j in [0:8] do
      byte := byte * 2 + bits[i * 8 + j]!
    entropy := entropy.push byte.toUInt8
  let checksum := (sha256 entropy).get! 0
  for i in [0:entropyLength / 4] do
    let expected := (checksum.toNat / 2 ^ (7 - i)) % 2
    if bits[entropyLength * 8 + i]! != expected then
      throw "Invalid BIP39 English mnemonic checksum"
  return entropy

private def xorBytes (a b : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:min a.size b.size] do
    result := result.push (a.get! i ^^^ b.get! i)
  return result

/-- RFC 8018 PBKDF2 using HMAC-SHA512. -/
def pbkdf2HmacSHA512 (password salt : ByteArray) (iterations outputBytes : Nat) : Except String ByteArray := do
  if iterations == 0 then throw "PBKDF2 iteration count must be positive"
  if outputBytes == 0 then throw "PBKDF2 output length must be positive"
  if (outputBytes + 63) / 64 > 0xffffffff then throw "PBKDF2 output is too long"
  let mut result := ByteArray.empty
  for block in [1:(outputBytes + 63) / 64 + 1] do
    let mut seed := salt
    for j in [0:4] do
      seed := seed.push ((block / 2 ^ (8 * (3 - j)) % 256).toUInt8)
    let mut u := hmacSHA512 password seed
    let mut t := u
    for _ in [1:iterations] do
      u := hmacSHA512 password u
      t := xorBytes t u
    result := result ++ t
  return result.extract 0 outputBytes

/-- BIP39 English phrase to 64-byte seed. Exact for the CLI's ASCII English
    mnemonic and empty passphrase. ASCII passphrases also work; Unicode
    passphrases require NFKD normalization and are unsupported here. -/
def mnemonicToSeedEnglish (mnemonic : String) (passphrase : String := "") : Except String ByteArray := do
  let _ ← mnemonicToEntropyEnglish mnemonic
  if passphrase.toList.any (fun c => c.toNat > 127) then
    throw "Unicode BIP39 passphrases require NFKD normalization"
  pbkdf2HmacSHA512 mnemonic.toUTF8 (("mnemonic" ++ passphrase).toUTF8) 2048 64

end LeanCrypto
