import Tornado.Domain.Catalog

/-!
Native parser for the integer forms accepted by JavaScript `Number` before
the TypeScript CLI's chain-ID check. Decimal forms use Lean's binary64 runtime
to reproduce rounding near the two supported chain IDs.
-/

namespace Tornado.Domain

private def decimalDigits (chars : List Char) : Bool :=
  chars.all (fun c => '0' ≤ c && c ≤ '9')

private def baseDigit (base : Nat) (c : Char) : Option Nat :=
  let value :=
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
    else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
    else base
  if value < base then some value else none

private def parseBase (base : Nat) (chars : List Char) : Option Nat := do
  if chars.isEmpty then none else do
    let mut value := 0
    for c in chars do
      let digit ← baseDigit base c
      value := value * base + digit
    return value

private def signedDecimal (chars : List Char) : Option Int := do
  let (negative, digits) :=
    match chars with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, chars)
  if digits.isEmpty || !decimalDigits digits then none else do
    let value ← (String.ofList digits).toNat?
    return if negative then -(Int.ofNat value) else Int.ofNat value

/-- `Number.isInteger`, determined from the binary64 representation. `Float`
    is part of Lean's pinned runtime, rather than a JS or external parser. -/
private def floatIsInteger (value : Float) : Bool :=
  if !value.isFinite then false
  else
    let bits := value.toBits.toNat
    let exponent := bits / 2 ^ 52 % 2048
    let fraction := bits % 2 ^ 52
    if exponent == 0 then fraction == 0
    else if exponent < 1023 then false
    else if exponent >= 1075 then true
    else fraction % 2 ^ (1075 - exponent) == 0

private def parseDecimal (raw : String) : Option Int := do
  let chars := raw.toList
  let (negative, unsigned) :=
    match chars with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | _ => (false, chars)
  let (mantissa, exponentText) ←
    match (String.ofList unsigned).toLower.splitOn "e" with
    | [mantissa] => some (mantissa, "0")
    | [mantissa, exponentText] => some (mantissa, exponentText)
    | _ => none
  let exponent ← signedDecimal exponentText.toList
  let parts := mantissa.splitOn "."
  let (whole, fraction) ←
    match parts with
    | [whole] => some (whole, "")
    | [whole, fraction] => some (whole, fraction)
    | _ => none
  let digits := whole ++ fraction
  if digits.isEmpty || !decimalDigits digits.toList then none else do
    let n ← digits.toNat?
    if n == 0 then return 0
    let scale := Int.ofNat fraction.length - exponent
    -- Clamp pathological exponents before calling the runtime's scientific
    -- conversion. For ordinary CLI inputs, classification uses binary64.
    if scale < -2048 then none
    else if scale > 2048 && (toString n).length + 324 < scale.toNat then some 0
    else if scale > 2048 then none
    else
      let magnitude : Float :=
        if scale <= 0 then Float.ofScientific n false (-scale).toNat
        else Float.ofScientific n true scale.toNat
      let value := if negative then -magnitude else magnitude
      if !floatIsInteger value then none
      else if value == (1.0 : Float) then some 1
      else if value == (11155111.0 : Float) then some 11155111
      else some 0

def parseJsInteger (raw : String) : Option Int :=
  let text := jsTrim raw
  if text.isEmpty then some 0
  else if text.startsWith "0x" || text.startsWith "0X" then
    (parseBase 16 (text.toList.drop 2)).map Int.ofNat
  else if text.startsWith "0b" || text.startsWith "0B" then
    (parseBase 2 (text.toList.drop 2)).map Int.ofNat
  else if text.startsWith "0o" || text.startsWith "0O" then
    (parseBase 8 (text.toList.drop 2)).map Int.ofNat
  else parseDecimal text

def parseChainInput (raw : String) : Except String ChainId :=
  match parseJsInteger raw with
  | none => .error "Chain must be 1 or 11155111."
  | some 1 => .ok .mainnet
  | some 11155111 => .ok .sepolia
  | some _ => .error "Only Ethereum mainnet (1) and Sepolia (11155111) are supported."

end Tornado.Domain
