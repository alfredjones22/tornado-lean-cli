import Lean
import Tornado.Protocol.TypedTransaction
import Tornado.Protocol.TypedTransactionDecode
import Tornado.Domain.NoteIdentity

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol.Rlp
open Tornado.Protocol.TypedTransaction
open Tornado.Protocol.TypedTransactionDecode

private def value (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def string (json : Json) (name : String) : Except String String := do
  (← value json name).getStr?

private def number (json : Json) (name : String) : Except String Nat := do
  let raw ← string json name
  match raw.toNat? with
  | some value => return value
  | none => throw s!"Invalid decimal {name}."

private def hex (raw : String) : Except String ByteArray :=
  parseHexBytes raw

private def natHex (raw : String) : Except String Nat := do
  let bytes ← hex raw
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def readAccess (json : Json) : Except String AccessEntry := do
  let address ← natHex (← string json "address")
  let keys ← (← value json "storageKeys").getArr?
  let mut storageKeys := #[]
  for item in keys do storageKeys := storageKeys.push (← hex (← item.getStr?))
  return { address, storageKeys }

private def readAuthorization (json : Json) : Except String Authorization7702 := do
  let chainId ← number json "chainId"
  let delegate ← natHex (← string json "address")
  let nonce ← number json "nonce"
  let yParity ← (← value json "yParity").getNat?
  let r ← natHex (← string json "r")
  let s ← natHex (← string json "s")
  return { chainId, delegate, nonce, signature := ⟨yParity, r, s⟩ }

private def readTransaction (json : Json) : Except String Transaction7702 := do
  let chainId ← number json "chainId"
  let nonce ← number json "nonce"
  let maxPriorityFeePerGas ← number json "maxPriorityFeePerGas"
  let maxFeePerGas ← number json "maxFeePerGas"
  let gas ← number json "gas"
  let to ← match (← value json "to") with
    | .null => pure none
    | .str address => pure (some (← natHex address))
    | _ => throw "Invalid transaction recipient."
  let valueAmount ← number json "value"
  let data ← hex (← string json "data")
  let rawAccess ← (← value json "accessList").getArr?
  let accessList ← rawAccess.mapM readAccess
  let rawAuthorizations ← (← value json "authorizationList").getArr?
  let authorizations ← rawAuthorizations.mapM readAuthorization
  let base : Transaction1559 :=
    ⟨chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas,
      to, valueAmount, data, accessList⟩
  return ⟨base, authorizations⟩

private def require (test : Bool) (message : String) : Except String Unit :=
  if test then .ok () else .error message

private def expectHex (actual : ByteArray) (expected label : String) : Except String Unit :=
  require ("0x" ++ bytesToHex actual == expected) s!"Typed transaction mismatch: {label}"

private def checkCase (json : Json) (privateKey : ByteArray) : Except String (Nat × Transaction7702) := do
  let name ← string json "name"
  let tx ← readTransaction (← value json "tx")
  let unsigned ← serialize7702 tx
  expectHex unsigned (← string json "unsigned") s!"{name} unsigned"
  let signingHash ← signingHash7702 tx
  expectHex signingHash (← string json "signingHash") s!"{name} signing hash"
  let simple : Signature := ⟨1, 1, 2⟩
  let simpleSigned ← serialize7702 tx (some simple)
  expectHex simpleSigned (← string json "simpleSigned") s!"{name} simple signature"
  let simpleHash ← transactionHash7702 tx simple
  expectHex simpleHash (← string json "simpleTransactionHash")
    s!"{name} simple transaction hash"
  let signed ← sign7702 tx privateKey
  expectHex signed.serialized (← string json "actualSigned")
    s!"{name} native signature"
  expectHex signed.transactionHash (← string json "actualTransactionHash")
    s!"{name} native transaction hash"
  require ((authorizationItems tx.authorizations).length == tx.authorizations.size)
    s!"{name} authorization count changed"
  for (fieldName, signedExpected) in
      [("unsigned", false), ("simpleSigned", true), ("actualSigned", true)] do
    let raw ← hex (← string json fieldName)
    let parsed ← decode7702 raw
    require (parsed.tx.base.chainId == tx.base.chainId &&
      parsed.tx.base.nonce == tx.base.nonce &&
      parsed.tx.base.value == tx.base.value &&
      parsed.tx.authorizations.size == tx.authorizations.size &&
      parsed.signature.isSome == signedExpected)
      s!"{name} decoded transaction fields changed"
  return (9, tx)

private def envelopeRaw (kind : UInt8) (fields : List ByteArray) : ByteArray :=
  (ByteArray.empty.push kind) ++ list fields

private def replaceField (fields : List ByteArray) (index : Nat)
    (replacement : ByteArray) : List ByteArray :=
  fields.take index ++ [replacement] ++ fields.drop (index + 1)

private def checkDecoderRejections (tx : Transaction7702) : Except String Unit := do
  let fields := unsignedFields7702 tx
  let valid ← serialize7702 tx
  require (!(decode7702 ((ByteArray.empty.push 0x05) ++ valid.extract 1 valid.size)).isOk)
    "Wrong typed transaction prefix accepted."
  require (!(decode7702 (valid.push 0)).isOk)
    "Trailing transaction bytes accepted."
  require (!(decode7702 (valid.extract 0 (valid.size - 1))).isOk)
    "Truncated transaction accepted."
  require (!(decode7702 (envelopeRaw 0x04
    (replaceField fields 0 (ByteArray.mk #[0x81, 0x01])))).isOk)
    "Overlong one-byte RLP integer accepted."
  require (!(decode7702 (envelopeRaw 0x04
    (replaceField fields 0 (ByteArray.mk #[0x82, 0x00, 0x01])))).isOk)
    "Leading-zero RLP integer accepted."
  require (!(decode7702 (envelopeRaw 0x04
    (replaceField fields 0 (ByteArray.mk #[0xb8, 0x01, 0x01])))).isOk)
    "Long-form RLP used for short atom."
  require (!(decode7702 (envelopeRaw 0x04
    (replaceField fields 8 (ByteArray.mk #[0xf8, 0x00])))).isOk)
    "Long-form RLP used for empty access list."
  let first := tx.authorizations[0]!
  let malformedTuple := list ((authorizationFields first).take 5)
  require (!(decode7702 (envelopeRaw 0x04
    (replaceField fields 9 (list [malformedTuple])))).isOk)
    "Short authorization tuple accepted."
  let malformedSigned := envelopeRaw 0x04
    (fields ++ [nat 0, nat 0, nat 2])
  require (!(decode7702 malformedSigned).isOk)
    "Zero transaction signature scalar accepted by decoder."
  require (!(decode7702 (envelopeRaw 0x04 (fields ++ [nat 0]))).isOk)
    "Partial transaction signature accepted."
  let type2 ← serialize1559 tx.base
  require (!(decode1559 (type2.push 0)).isOk)
    "Trailing type-2 bytes accepted."
  require (!(decode1559 (envelopeRaw 0x02
    (replaceField (fields.take 9) 0 (ByteArray.mk #[0x81, 0x01])))).isOk)
    "Noncanonical type-2 integer accepted."

private def checkRejections (tx : Transaction7702) : Except String Unit := do
  let first := tx.authorizations[0]!
  require (!(serialize7702 { tx with base := { tx.base with chainId := 0 } }).isOk)
    "Zero transaction chain accepted."
  require (!(serialize7702 { tx with base := { tx.base with chainId := 2 ^ 256 } }).isOk)
    "Oversized transaction chain accepted."
  require (!(serialize7702 { tx with base := { tx.base with to := some (2 ^ 160) } }).isOk)
    "Oversized recipient accepted."
  require (!(serialize7702 { tx with base := { tx.base with maxPriorityFeePerGas := tx.base.maxFeePerGas + 1 } }).isOk)
    "Tip above fee cap accepted."
  require (!(serialize7702 { tx with authorizations := #[{ first with delegate := 2 ^ 160 }] }).isOk)
    "Oversized delegate accepted."
  require (!(serialize7702 { tx with authorizations := #[{ first with nonce := 2 ^ 256 }] }).isOk)
    "Oversized authorization nonce accepted."
  require (!(serialize7702 { tx with authorizations := #[{ first with signature := { first.signature with yParity := 2 } }] }).isOk)
    "Invalid authorization parity accepted."
  require (!(serialize7702 { tx with authorizations := #[{ first with signature := { first.signature with r := 0 } }] }).isOk)
    "Zero authorization signature scalar accepted."
  require (!(serialize7702 tx (some ⟨2, 1, 2⟩)).isOk)
    "Invalid transaction parity accepted."
  require (!(serialize7702 tx (some ⟨0, 0, 2⟩)).isOk)
    "Zero transaction signature scalar accepted."

private def check (json : Json) : Except String Nat := do
  let privateKey ← hex (← string json "privateKey")
  let cases ← (← value json "cases").getArr?
  let mut count := 0
  let mut first : Option Transaction7702 := none
  for item in cases do
    let (n, tx) ← checkCase item privateKey
    count := count + n
    if first.isNone then first := some tx
  let some tx := first | throw "No transaction fixture."
  let signed1559 ← sign1559 tx.base privateKey
  let eip1559 ← value json "eip1559"
  expectHex signed1559.serialized (← string eip1559 "actualSigned")
    "native EIP-1559 signature"
  expectHex signed1559.transactionHash (← string eip1559 "actualTransactionHash")
    "native EIP-1559 transaction hash"
  let unsigned1559 ← serialize1559 tx.base
  let decodedUnsigned1559 ← decode1559 unsigned1559
  require (decodedUnsigned1559.signature.isNone &&
    decodedUnsigned1559.tx.chainId == tx.base.chainId)
    "Unsigned type-2 transaction decoded incorrectly."
  let decodedSigned1559 ← decode1559 signed1559.serialized
  require (decodedSigned1559.signature.isSome &&
    decodedSigned1559.tx.chainId == tx.base.chainId)
    "Signed type-2 transaction decoded incorrectly."
  count := count + 4
  let signedAuthorizations ← (← value json "signedAuthorizations").getArr?
  for item in signedAuthorizations do
    let expected ← readAuthorization item
    let actual ← signAuthorization7702 expected.chainId expected.delegate
      expected.nonce privateKey
    require (actual.chainId == expected.chainId &&
      actual.delegate == expected.delegate && actual.nonce == expected.nonce &&
      actual.signature.yParity == expected.signature.yParity &&
      actual.signature.r == expected.signature.r &&
      actual.signature.s == expected.signature.s)
      "Native EIP-7702 authorization signature differs from viem."
    count := count + 1
  checkRejections tx
  checkDecoderRejections tx
  return count

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/typed-transactions.json"
  match Json.parse raw >>= check with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok count =>
      IO.println s!"PASS: {count} viem EIP-1559/EIP-7702 typed transaction checks and 22 rejections"
      return 0
