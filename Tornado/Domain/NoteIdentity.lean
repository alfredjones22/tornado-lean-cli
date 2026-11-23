import Tornado.Domain.Notes
import Tornado.Crypto.Pedersen

/-!
Classic Tornado public note identifiers computed natively in Lean. The raw
62-byte note preimage is split into two 31-byte secret segments; the first
31 bytes yield the nullifier hash, while all 62 yield the commitment.
-/

namespace Tornado.Domain

structure NoteIdentity where
  commitment : String
  nullifierHash : String
  deriving Repr, BEq, Inhabited

private def hexNibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode ASCII hex without relying on Node or viem. An optional lowercase
    `0x` prefix is accepted. Odd length or non-hex input fails. -/
def parseHexBytes (raw : String) : Except String ByteArray := do
  let chars := (if raw.startsWith "0x" then raw.toList.drop 2 else raw.toList).toArray
  if chars.size % 2 != 0 then throw "Hex input has an odd number of digits."
  let mut bytes := ByteArray.empty
  for index in [0:chars.size / 2] do
    let some hi := hexNibble chars[index * 2]!
      | throw "Hex input contains a non-hex digit."
    let some lo := hexNibble chars[index * 2 + 1]!
      | throw "Hex input contains a non-hex digit."
    bytes := bytes.push (UInt8.ofNat (hi * 16 + lo))
  return bytes

private def hexChar (value : Nat) : Char :=
  ("0123456789abcdef".toList[value]?).getD '0'

/-- Encode a bounded natural number as exactly 32 big-endian bytes with `0x`. -/
def toHex32 (value : Nat) : Except String String := do
  if value >= 2 ^ 256 then throw "Value does not fit in bytes32."
  let digits := (List.range 64).map fun index =>
    hexChar ((value / (16 ^ (63 - index))) % 16)
  return "0x" ++ String.ofList digits

def noteIdentity (note : ParsedNote) : Except String NoteIdentity := do
  if note.preimage.length != 124 then throw "Classic note preimage must contain 62 bytes."
  let bytes ← parseHexBytes note.preimage
  if bytes.size != 62 then throw "Classic note preimage must contain 62 bytes."
  let commitmentX ← Tornado.Crypto.pedersenX bytes
  let nullifierX ← Tornado.Crypto.pedersenX (bytes.extract 0 31)
  return { commitment := (← toHex32 commitmentX), nullifierHash := (← toHex32 nullifierX) }

end Tornado.Domain
