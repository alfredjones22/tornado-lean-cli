import Lean
import Tornado.Protocol.Abi
import Tornado.Domain.NoteIdentity

/-! Bounded ABI encoding for Safe Transaction Builder method imports. All
encoding is native Lean. The accepted types are integer widths, addresses,
booleans, fixed/dynamic bytes, UTF-8 strings, arrays and named/positional
tuples. A maximum nesting depth of 12 and the existing 16 KiB calldata bound
apply before a call can reach review. No ABI value executes code. -/

namespace Tornado.Protocol.ImportedAbi

open Lean Tornado.Crypto Tornado.Domain

def maxEncodedBytes : Nat := 16384
def maxElements : Nat := 1024
def maxDepth : Nat := 12

inductive Kind where
  | uint (bits : Nat)
  | sint (bits : Nat)
  | address
  | boolean
  | fixedBytes (size : Nat)
  | bytes
  | text
  | array (element : Kind) (length : Option Nat)
  | tuple (components : Array (String × Kind))
  deriving Inhabited

private def bad : String := "Invalid or unsupported imported ABI argument."

private def getString (value : Json) (key : String) : Except String String := do
  (← value.getObjVal? key).getStr?

private def optionalName (value : Json) : Except String String :=
  match value.getObjVal? "name" with
  | .error _ => .ok ""
  | .ok .null => .ok ""
  | .ok value => value.getStr?

private def unsignedDecimal (value : String) : Except String Nat := do
  if value.isEmpty || !value.toList.all (fun char => '0' ≤ char && char ≤ '9') then
    throw bad
  let some parsed := value.toNat? | throw bad
  return parsed

private def integerWidth (raw : String) : Except String Nat := do
  let width ← if raw.isEmpty then pure 256 else unsignedDecimal raw
  if width == 0 || width > 256 || width % 8 != 0 then throw bad
  return width

private def parseKind : Nat → Json → String → Except String Kind
  | 0, _, _ => .error "Imported ABI arguments are nested too deeply."
  | fuel + 1, parameter, raw => do
    if raw.utf8ByteSize > 256 then throw "Imported ABI type description is too long."
    if raw.endsWith "]" then
      let parts := raw.splitOn "["
      if parts.length < 2 then throw bad
      let suffix := parts.getLast!
      let digits := String.ofList (suffix.toList.dropLast)
      let length ← if digits.isEmpty then pure none else do
        let length ← unsignedDecimal digits
        if length > maxElements then throw "Imported ABI array exceeds 1024 elements."
        pure (some length)
      let base := String.intercalate "[" parts.dropLast
      return .array (← parseKind fuel parameter base) length
    else if raw == "tuple" then
      let parts ← (← parameter.getObjVal? "components").getArr?
      if parts.size > maxElements then throw "Imported ABI tuple has too many components."
      let components ← parts.mapM fun part => do
        return (← optionalName part, ← parseKind fuel part (← getString part "type"))
      return .tuple components
    else if raw.startsWith "uint" then
      return .uint (← integerWidth (String.ofList (raw.toList.drop 4)))
    else if raw.startsWith "int" then
      return .sint (← integerWidth (String.ofList (raw.toList.drop 3)))
    else if raw == "address" then return .address
    else if raw == "bool" then return .boolean
    else if raw == "bytes" then return .bytes
    else if raw == "string" then return .text
    else if raw.startsWith "bytes" then
      let count ← unsignedDecimal (String.ofList (raw.toList.drop 5))
      if count == 0 || count > 32 then throw bad
      return .fixedBytes count
    else throw "Unsupported imported ABI type."

def parseParameter (parameter : Json) : Except String (String × Kind) := do
  return (← optionalName parameter,
    ← parseKind (maxDepth + 1) parameter (← getString parameter "type"))

/-- Match viem's signature formatting, including its preservation of `uint`
and `int` aliases. Tuple component names never enter the selector. -/
private def signatureType : Nat → Json → Except String String
  | 0, _ => .error bad
  | fuel + 1, parameter => do
    let raw ← getString parameter "type"
    if raw.startsWith "tuple" then
      let components ← (← parameter.getObjVal? "components").getArr?
      let parts ← components.mapM (signatureType fuel)
      return "(" ++ String.intercalate "," parts.toList ++ ")" ++
        String.ofList (raw.toList.drop 5)
    return raw

private def dynamic : Nat → Kind → Bool
  | 0, _ => true
  | fuel + 1, kind =>
    match kind with
    | .bytes | .text | .array _ none => true
    | .array element (some _) => dynamic fuel element
    | .tuple components => components.any (fun (_, kind) => dynamic fuel kind)
    | _ => false

private def checkSize (bytes : ByteArray) : Except String ByteArray := do
  if bytes.size > maxEncodedBytes then throw "Imported ABI calldata exceeds 16 KiB."
  return bytes

private def join (left right : ByteArray) : Except String ByteArray := do
  if left.size + right.size > maxEncodedBytes then
    throw "Imported ABI calldata exceeds 16 KiB."
  return left ++ right

private structure Encoded where
  isDynamic : Bool
  bytes : ByteArray
  deriving Inhabited

private def contribution (value : Encoded) : Nat :=
  value.bytes.size + if value.isDynamic then 32 else 0

private def checkBudget (size : Nat) : Except String Unit := do
  if size > maxEncodedBytes then throw "Imported ABI calldata exceeds 16 KiB."

/-- Offsets are relative to the beginning of this tuple's head. A dynamic
array puts its length word before this encoding, as required by Solidity. -/
private def encodeTuple (values : Array Encoded) : Except String ByteArray := do
  let headSize := values.foldl
    (fun size value => size + if value.isDynamic then 32 else value.bytes.size) 0
  if headSize > maxEncodedBytes then throw "Imported ABI calldata exceeds 16 KiB."
  let mut head := ByteArray.empty
  let mut tail := ByteArray.empty
  for value in values do
    if value.isDynamic then
      head ← join head (← Abi.uintWord (headSize + tail.size))
      tail ← join tail value.bytes
    else head ← join head value.bytes
  join head tail

private def compound (value : Json) : Except String Json := do
  match value with
  | .str raw => Json.parse raw |>.mapError (fun _ => "Use JSON for imported tuples and arrays.")
  | value => return value

private def signedInteger (value : Json) : Except String Int := do
  match value with
  | .str raw =>
    if raw.length > 79 then throw bad
    let digits := if raw.startsWith "-" then String.ofList (raw.toList.drop 1) else raw
    let number ← unsignedDecimal digits
    return if raw.startsWith "-" then -(Int.ofNat number) else Int.ofNat number
  | .num _ =>
    let number ← value.getInt?
    if number.natAbs > 9007199254740991 then
      throw "Quote large integers in contract call JSON."
    return number
  | _ => throw "Imported ABI integer must be in base units."

private def hexBytes (value : Json) : Except String ByteArray := do
  let raw ← value.getStr?
  if !raw.startsWith "0x" || raw.length % 2 != 0 ||
      raw.utf8ByteSize > 2 * maxEncodedBytes + 2 then throw bad
  parseHexBytes raw

private def addressWord (value : Json) : Except String ByteArray := do
  let raw ← value.getStr?
  let bytes ← hexBytes value
  if bytes.size != 20 then throw bad
  let digits := String.ofList (raw.toList.drop 2)
  if digits != digits.toLower && digits != digits.toUpper then
    let hash := keccak256 digits.toLower.toUTF8
    let chars := digits.toList.toArray
    for i in [0:chars.size] do
      let byte := hash[i / 2]!.toNat
      let nibble := if i % 2 == 0 then byte / 16 else byte % 16
      let expected := if nibble >= 8 then chars[i]!.toUpper else chars[i]!.toLower
      if chars[i]! != expected then throw "Imported ABI address has an invalid checksum."
  return ⟨Array.replicate 12 0⟩ ++ bytes

private def encodeValue : Nat → Kind → Json → Except String Encoded
  | 0, _, _ => .error "Imported ABI arguments are nested too deeply."
  | fuel + 1, kind, value => do
    match kind with
    | .uint bits =>
      let number ← signedInteger value
      if number < 0 || number >= Int.ofNat (2 ^ bits) then throw bad
      return ⟨false, ← Abi.uintWord number.toNat⟩
    | .sint bits =>
      let number ← signedInteger value
      let half : Int := Int.ofNat (2 ^ (bits - 1))
      if number < -half || number >= half then throw bad
      let word := if number < 0 then 2 ^ 256 - number.natAbs else number.toNat
      return ⟨false, ← Abi.uintWord word⟩
    | .address => return ⟨false, ← addressWord value⟩
    | .boolean =>
      let number ← if value == .bool true || value == toJson ("true" : String) then pure 1
        else if value == .bool false || value == toJson ("false" : String) then pure 0
        else throw "Invalid imported ABI boolean."
      return ⟨false, ← Abi.uintWord number⟩
    | .fixedBytes size =>
      let bytes ← hexBytes value
      if bytes.size != size then throw bad
      return ⟨false, bytes ++ ⟨Array.replicate (32 - size) 0⟩⟩
    | .bytes =>
      let bytes ← hexBytes value
      return ⟨true, ← checkSize (← Abi.dynamicBytes bytes)⟩
    | .text =>
      let raw ← value.getStr?
      if raw.utf8ByteSize > maxEncodedBytes then throw "Imported ABI string exceeds 16 KiB."
      return ⟨true, ← checkSize (← Abi.dynamicBytes raw.toUTF8)⟩
    | .array element length =>
      let values ← (← compound value).getArr?
      if values.size > maxElements || length.any (· != values.size) then
        throw "Invalid imported ABI array."
      let mut encoded := #[]
      let mut size := 0
      for value in values do
        let item ← encodeValue fuel element value
        size := size + contribution item
        checkBudget size
        encoded := encoded.push item
      let body ← encodeTuple encoded
      if length.isNone then
        return ⟨true, ← join (← Abi.uintWord values.size) body⟩
      return ⟨dynamic fuel element, body⟩
    | .tuple components =>
      let value ← compound value
      let mut values := #[]
      let mut size := 0
      for index in [0:components.size] do
        let (name, kind) := components[index]!
        let part ← match value with
          | .arr items =>
            match items[index]? with
            | some part => pure part
            | none => throw "Missing imported ABI tuple argument."
          | .obj _ => value.getObjVal? name
          | _ => throw "Invalid imported ABI tuple."
        let item ← encodeValue fuel kind part
        size := size + contribution item
        checkBudget size
        values := values.push item
      return ⟨values.any (·.isDynamic), ← encodeTuple values⟩

/-- Encode a Safe `contractMethod` and its named input-value object. The
result is canonical function calldata and is bounded before allocation grows
beyond the contract-call limit. An absent value is accepted only when the
function has no inputs. -/
def encodeFunctionData (method values : Json) (valueWei : Nat) : Except String ByteArray := do
  let name ← getString method "name"
  if name.isEmpty || name.utf8ByteSize > 1024 then throw "Invalid imported contract method."
  let inputs ← (← method.getObjVal? "inputs").getArr?
  if inputs.size > maxElements then throw "Imported ABI method has too many arguments."
  let payable ← match method.getObjVal? "payable" with
    | .error _ | .ok .null => pure false
    | .ok (.bool payable) => pure payable
    | _ => throw "Imported contract method payable flag must be boolean."
  if valueWei > 0 && !payable then throw "Imported contract method is not payable."
  let parameters ← inputs.mapM parseParameter
  let types ← inputs.mapM (signatureType (maxDepth + 1))
  let mut encoded := #[]
  let mut size := 0
  for (name, kind) in parameters do
    let argument ← values.getObjVal? name
    let item ← encodeValue (maxDepth + 1) kind argument
    size := size + contribution item
    checkBudget size
    encoded := encoded.push item
  let selector := Abi.selector (name ++ "(" ++ String.intercalate "," types.toList ++ ")")
  join selector (← encodeTuple encoded)

end Tornado.Protocol.ImportedAbi
