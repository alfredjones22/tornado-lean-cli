/-!
Exact nonnegative decimal token-unit conversion. This module has no FFI or
JavaScript dependency. CLI-facing error text follows the captured TypeScript
`parseAmount` implementation for ASCII input.
-/

namespace Tornado.Domain

def jsWhitespace (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || n == 0x20 || n == 0xa0 || n == 0x1680 ||
    (0x2000 ≤ n && n ≤ 0x200a) || n == 0x2028 || n == 0x2029 ||
    n == 0x202f || n == 0x205f || n == 0x3000 || n == 0xfeff

def jsTrim (value : String) : String :=
  String.ofList (((value.toList.dropWhile jsWhitespace).reverse.dropWhile jsWhitespace).reverse)

def jsUtf16Length (value : String) : Nat :=
  value.toList.foldl (fun size c => size + if c.toNat > 0xffff then 2 else 1) 0

private def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def allDigits (s : String) : Bool := !s.isEmpty && s.toList.all isAsciiDigit

private def validWhole (s : String) : Bool :=
  s == "0" || (s.toList.head? != some '0' && allDigits s)

structure DecimalParts where
  whole : String
  fraction : String
  deriving Repr, BEq, Inhabited

def decimalParts (s : String) : Option DecimalParts :=
  match s.splitOn "." with
  | [whole] =>
      if validWhole whole then some ⟨whole, ""⟩ else none
  | [whole, fraction] =>
      if validWhole whole && allDigits fraction then some ⟨whole, fraction⟩ else none
  | _ => none

def parseUnitsExact (s : String) (decimals : Nat) : Option Nat := do
  let parts ← decimalParts s
  if parts.fraction.length > decimals then none
  let whole ← parts.whole.toNat?
  let fraction ← if parts.fraction.isEmpty then some 0 else parts.fraction.toNat?
  return whole * (10 ^ decimals) + fraction * (10 ^ (decimals - parts.fraction.length))

def parseAmount (input : String) (decimals : Nat) : Except String Nat := do
  let value := jsTrim input
  if jsUtf16Length value > 64 then
    throw "Enter a smaller amount."
  let some parts := decimalParts value
    | throw "Enter a positive amount, such as 1.75."
  if parts.fraction.length > decimals then
    throw s!"Use at most {decimals} decimal places."
  let some amount := parseUnitsExact value decimals
    | throw "Enter a positive amount, such as 1.75."
  if amount == 0 then throw "Amount must be greater than zero."
  return amount

def formatUnitsExact (amount decimals : Nat) : String := Id.run do
  let factor := 10 ^ decimals
  let whole := amount / factor
  let remainder := amount % factor
  if decimals == 0 || remainder == 0 then return toString whole
  let raw := toString remainder
  let padded := String.ofList (List.replicate (decimals - raw.length) '0') ++ raw
  let fraction := String.ofList ((padded.toList.reverse.dropWhile (· == '0')).reverse)
  return s!"{whole}.{fraction}"

end Tornado.Domain
