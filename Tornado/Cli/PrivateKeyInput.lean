/-!
Byte-level parsing of a protected hex EOA key file. The input is bounded and
never converted to a Lean `String`, which avoids the earlier UTF-8 and trimmed
String copies of the private key. The returned `ByteArray` remains Lean-managed
secret memory: this module does not make signing constant-time or zeroizing.
-/

namespace Tornado.Cli.PrivateKeyInput

private def invalid : String :=
  "Key file must contain only a 32-byte hex private key."

private def byte (input : ByteArray) (index : Nat) : Nat :=
  input.data[index]!.toNat

private def asciiWhitespace (value : Nat) : Bool :=
  (9 <= value && value <= 13) || value == 0x20

/-- Number of bytes in a JavaScript-trim whitespace code point at `index`.
    This recognizes the same code points as `Domain.jsWhitespace` without
    decoding or copying the key-bearing middle of the input. -/
private def whitespaceAt (input : ByteArray) (index : Nat) : Nat := Id.run do
  if index >= input.size then return 0
  let a := byte input index
  if asciiWhitespace a then return 1
  if index + 2 <= input.size && a == 0xc2 &&
      byte input (index + 1) == 0xa0 then return 2
  if index + 3 > input.size then return 0
  let b := byte input (index + 1)
  let c := byte input (index + 2)
  if a == 0xe1 && b == 0x9a && c == 0x80 then return 3
  if a == 0xe2 && b == 0x80 &&
      ((0x80 <= c && c <= 0x8a) || c == 0xa8 || c == 0xa9 || c == 0xaf) then
    return 3
  if a == 0xe2 && b == 0x81 && c == 0x9f then return 3
  if a == 0xe3 && b == 0x80 && c == 0x80 then return 3
  if a == 0xef && b == 0xbb && c == 0xbf then return 3
  return 0

private def whitespaceBefore (input : ByteArray) (exclusiveEnd : Nat) : Nat :=
  if exclusiveEnd >= 3 && whitespaceAt input (exclusiveEnd - 3) == 3 then 3
  else if exclusiveEnd >= 2 && whitespaceAt input (exclusiveEnd - 2) == 2 then 2
  else if exclusiveEnd >= 1 && whitespaceAt input (exclusiveEnd - 1) == 1 then 1
  else 0

private def nibble (value : Nat) : Option Nat :=
  if 0x30 <= value && value <= 0x39 then some (value - 0x30)
  else if 0x61 <= value && value <= 0x66 then some (value - 0x61 + 10)
  else if 0x41 <= value && value <= 0x46 then some (value - 0x41 + 10)
  else none

/-- Parse a protected file's exact 32-byte hex key, allowing surrounding
    JavaScript whitespace. Malformed bytes never appear in the error. -/
def parse (input : ByteArray) : Except String ByteArray := do
  if input.size > 1024 then throw invalid
  let mut start := 0
  while start < input.size do
    let skip := whitespaceAt input start
    if skip == 0 then break
    start := start + skip
  let mut stop := input.size
  while stop > start do
    let skip := whitespaceBefore input stop
    if skip == 0 then break
    stop := stop - skip
  if stop - start != 66 || byte input start != 0x30 ||
      byte input (start + 1) != 0x78 then throw invalid
  let mut result := ByteArray.empty
  for i in [0:32] do
    let some hi := nibble (byte input (start + 2 + 2 * i))
      | throw invalid
    let some lo := nibble (byte input (start + 3 + 2 * i))
      | throw invalid
    result := result.push (UInt8.ofNat (16 * hi + lo))
  return result

end Tornado.Cli.PrivateKeyInput
