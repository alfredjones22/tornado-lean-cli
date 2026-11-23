import Tornado.Protocol.TypedTransaction
import Tornado.Protocol.Abi

/-!
Strict, bounded RLP decoding for the two typed transaction shapes used in the
native library. An accepted result carries a kernel-checked equality saying
that the native serializer reproduces the exact input bytes. This rejects
nonminimal RLP, extra fields, trailing data, and alternate encodings.

The decoder authenticates neither the signer nor any chain-supplied data. It
is not a transaction receipt or EIP-7702 delegation validator.
-/

namespace Tornado.Protocol.TypedTransactionDecode

open Tornado.Crypto
open Tornado.Protocol.Rlp
open Tornado.Protocol.TypedTransaction

structure Item where
  isList : Bool
  start : Nat
  payloadStart : Nat
  stop : Nat
  deriving Inhabited

private def natOfBytes (value : ByteArray) : Nat :=
  value.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def readLongLength (raw : ByteArray) (start count : Nat) : Except String Nat := do
  if count == 0 || count > 8 || start + count > raw.size then
    throw "Invalid long RLP length."
  let digits := raw.extract start (start + count)
  if digits[0]!.toNat == 0 then throw "Nonminimal long RLP length."
  let length := natOfBytes digits
  if length <= 55 then throw "Long RLP length used for a short item."
  return length

private def checkedItem (raw : ByteArray) (isList : Bool)
    (start payloadStart length : Nat) : Except String Item := do
  if payloadStart + length > raw.size then throw "Truncated RLP item."
  return ⟨isList, start, payloadStart, payloadStart + length⟩

/-- Parse one RLP header and bound its byte range without recursively parsing
    its children. Nested lists are traversed by `splitList` below. -/
def readItem (raw : ByteArray) (start : Nat) : Except String Item := do
  if start >= raw.size then throw "Missing RLP item."
  let lead := raw[start]!.toNat
  if lead < 0x80 then
    return ⟨false, start, start, start + 1⟩
  else if lead <= 0xb7 then
    let length := lead - 0x80
    let item ← checkedItem raw false start (start + 1) length
    if length == 1 && raw[item.payloadStart]!.toNat < 0x80 then
      throw "Nonminimal one-byte RLP atom."
    return item
  else if lead <= 0xbf then
    let count := lead - 0xb7
    let length ← readLongLength raw (start + 1) count
    return (← checkedItem raw false start (start + 1 + count) length)
  else if lead <= 0xf7 then
    return (← checkedItem raw true start (start + 1) (lead - 0xc0))
  else
    let count := lead - 0xf7
    let length ← readLongLength raw (start + 1) count
    return (← checkedItem raw true start (start + 1 + count) length)

/-- Split one RLP list into its direct children. The byte position strictly
    advances and no child may extend past its parent. -/
def splitList (raw : ByteArray) (parent : Item) : Except String (Array Item) := do
  if !parent.isList then throw "Expected RLP list."
  let mut children := #[]
  let mut cursor := parent.payloadStart
  while cursor < parent.stop do
    let item ← readItem raw cursor
    if item.stop > parent.stop || item.stop <= cursor then
      throw "RLP child exceeds its parent."
    children := children.push item
    if children.size > 4096 then throw "RLP list has too many children."
    cursor := item.stop
  if cursor != parent.stop then throw "RLP list length mismatch."
  return children

private def field (items : Array Item) (index : Nat) : Except String Item :=
  match items[index]? with
  | some item => .ok item
  | none => .error "Typed transaction field is missing."

private def atom (raw : ByteArray) (item : Item) : Except String ByteArray := do
  if item.isList then throw "Expected RLP byte string."
  return raw.extract item.payloadStart item.stop

private def unsigned (raw : ByteArray) (item : Item) : Except String Nat := do
  let payload ← atom raw item
  if payload.size > 32 || (payload.size > 0 && payload[0]!.toNat == 0) then
    throw "Noncanonical or oversized RLP integer."
  return natOfBytes payload

private def fixedAddress (raw : ByteArray) (item : Item) : Except String Nat := do
  let payload ← atom raw item
  if payload.size != 20 then throw "RLP address must have 20 bytes."
  return natOfBytes payload

private def recipient (raw : ByteArray) (item : Item) : Except String (Option Nat) := do
  let payload ← atom raw item
  if payload.isEmpty then return none
  if payload.size != 20 then throw "RLP recipient must be 20 bytes or empty."
  return some (natOfBytes payload)

private def decodeAccess (raw : ByteArray) (parent : Item) : Except String (Array AccessEntry) := do
  let tuples ← splitList raw parent
  let mut result := #[]
  for tuple in tuples do
    let pair ← splitList raw tuple
    if pair.size != 2 then throw "Access-list tuple must contain two items."
    let address ← fixedAddress raw (← field pair 0)
    let keyItems ← splitList raw (← field pair 1)
    let mut storageKeys := #[]
    for key in keyItems do
      let bytes ← atom raw key
      if bytes.size != 32 then throw "Access-list storage key must be bytes32."
      storageKeys := storageKeys.push bytes
    result := result.push ⟨address, storageKeys⟩
  return result

private def decodeSignature (raw : ByteArray) (fields : Array Item)
    (start : Nat) : Except String Signature := do
  let yParity ← unsigned raw (← field fields start)
  let r ← unsigned raw (← field fields (start + 1))
  let s ← unsigned raw (← field fields (start + 2))
  if yParity > 1 || r == 0 || s == 0 ||
      r >= secp256k1Order || s >= secp256k1Order then
    throw "Invalid canonical typed transaction signature."
  return ⟨yParity, r, s⟩

private def decodeBase (raw : ByteArray) (fields : Array Item) : Except String Transaction1559 := do
  let chainId ← unsigned raw (← field fields 0)
  let nonce ← unsigned raw (← field fields 1)
  let maxPriorityFeePerGas ← unsigned raw (← field fields 2)
  let maxFeePerGas ← unsigned raw (← field fields 3)
  let gas ← unsigned raw (← field fields 4)
  let to ← recipient raw (← field fields 5)
  let value ← unsigned raw (← field fields 6)
  let data ← atom raw (← field fields 7)
  let accessList ← decodeAccess raw (← field fields 8)
  let tx : Transaction1559 :=
    ⟨chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas,
      to, value, data, accessList⟩
  validateTransaction tx
  return tx

private def decodeAuthorizations (raw : ByteArray) (parent : Item) :
    Except String (Array Authorization7702) := do
  let tuples ← splitList raw parent
  let mut result := #[]
  for tuple in tuples do
    let fields ← splitList raw tuple
    if fields.size != 6 then throw "EIP-7702 authorization must have six fields."
    let chainId ← unsigned raw (← field fields 0)
    let delegate ← fixedAddress raw (← field fields 1)
    let nonce ← unsigned raw (← field fields 2)
    let signature ← decodeSignature raw fields 3
    let auth : Authorization7702 := ⟨chainId, delegate, nonce, signature⟩
    validateAuthorization auth
    result := result.push auth
  return result

private def envelope (raw : ByteArray) (kind : UInt8) : Except String (Array Item) := do
  if raw.size < 2 || raw[0]! != kind then
    throw "Wrong typed transaction prefix."
  let root ← readItem raw 1
  if !root.isList || root.stop != raw.size then
    throw "Typed transaction has non-list or trailing bytes."
  return (← splitList raw root)

/-- A decoded type-2 transaction has exactly its original canonical bytes.
    The proof is constructed only after byte-for-byte reserialization. -/
structure Canonical1559 (raw : ByteArray) where
  tx : Transaction1559
  signature : Option Signature
  exact : serialize1559 tx signature = .ok raw

/-- A decoded type-4 transaction has exactly its original canonical bytes. -/
structure Canonical7702 (raw : ByteArray) where
  tx : Transaction7702
  signature : Option Signature
  exact : serialize7702 tx signature = .ok raw

def decode1559 (raw : ByteArray) : Except String (Canonical1559 raw) := do
  let fields ← envelope raw 0x02
  if fields.size != 9 && fields.size != 12 then
    throw "EIP-1559 field count must be nine or twelve."
  let tx ← decodeBase raw fields
  let signature ← if fields.size == 12 then
      some <$> decodeSignature raw fields 9
    else pure none
  match hc : serialize1559 tx signature with
  | .error error => throw error
  | .ok canonical =>
    if he : canonical == raw then
      have same : canonical = raw := Tornado.Protocol.Abi.byteArray_eq_of_beq he
      return ⟨tx, signature, by simpa [same] using hc⟩
    else throw "EIP-1559 RLP is not canonical."

def decode7702 (raw : ByteArray) : Except String (Canonical7702 raw) := do
  let fields ← envelope raw 0x04
  if fields.size != 10 && fields.size != 13 then
    throw "EIP-7702 field count must be ten or thirteen."
  let base ← decodeBase raw fields
  let authorizations ← decodeAuthorizations raw (← field fields 9)
  let tx : Transaction7702 := ⟨base, authorizations⟩
  let signature ← if fields.size == 13 then
      some <$> decodeSignature raw fields 10
    else pure none
  match hc : serialize7702 tx signature with
  | .error error => throw error
  | .ok canonical =>
    if he : canonical == raw then
      have same : canonical = raw := Tornado.Protocol.Abi.byteArray_eq_of_beq he
      return ⟨tx, signature, by simpa [same] using hc⟩
    else throw "EIP-7702 RLP is not canonical."

/-- Accepted decoded type-2 bytes exactly reserialize. -/
theorem decode1559_exact (raw : ByteArray) (parsed : Canonical1559 raw)
    (_h : decode1559 raw = .ok parsed) :
    serialize1559 parsed.tx parsed.signature = .ok raw := parsed.exact

/-- Accepted decoded type-4 bytes exactly reserialize. -/
theorem decode7702_exact (raw : ByteArray) (parsed : Canonical7702 raw)
    (_h : decode7702 raw = .ok parsed) :
    serialize7702 parsed.tx parsed.signature = .ok raw := parsed.exact

end Tornado.Protocol.TypedTransactionDecode

#print axioms Tornado.Protocol.TypedTransactionDecode.decode1559_exact
#print axioms Tornado.Protocol.TypedTransactionDecode.decode7702_exact
