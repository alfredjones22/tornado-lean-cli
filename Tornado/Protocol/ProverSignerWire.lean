import Tornado.Protocol.ProverWorkerWire
import Tornado.Protocol.Rlp
import Tornado.Crypto.Secp256k1

/-! Strict public-only records for the experimental note-derived signer.
The selected metadata association is private session data; no preimage or
key may enter these records. An authorization can only use the pinned
Simple7702 delegate, selected chain, and nonce zero. -/

namespace Tornado.Protocol.ProverSignerWire

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol.ProverWorkerWire

def delegate : Nat := 0xe6cae83bde06e4c305530e199d7217f42808555b

private def bad : String := "Invalid isolated signer record"

def metadataHash (metadata : Metadata) : ByteArray := keccak256 metadata.encode.toUTF8

private def bytesField (json : Json) (name : String) (size : Nat) : Except String ByteArray := do
  let raw ← (← json.getObjVal? name).getStr?
  let bytes ← parseHexBytes raw
  if bytes.size != size || raw != "0x" ++ bytesToHex bytes then throw bad
  return bytes

private def numberField (json : Json) (name : String) : Except String Nat := do
  let raw ← (← json.getObjVal? name).getStr?
  if raw.isEmpty || raw.length > 78 then throw bad
  let some value := raw.toNat? | throw bad
  if toString value != raw then throw bad
  return value

private def checkHeader (json : Json) (kind : String) : Except String Unit := do
  if (← (← json.getObjVal? "version").getNat?) != 1 ||
      (← (← json.getObjVal? "kind").getStr?) != kind then throw bad

private def hexJson (bytes : ByteArray) : Json := toJson ("0x" ++ bytesToHex bytes)

def canonicalSignature (signature : ByteArray) : Bool := Id.run do
  if signature.size != 65 then return false
  let word (start : Nat) := (signature.extract start (start + 32)).data.foldl
    (fun n byte => n * 256 + byte.toNat) 0
  let r := word 0
  let s := word 32
  return r > 0 && r < secp256k1Order && s > 0 && s <= secp256k1Order / 2 &&
    (signature[64]! == 27 || signature[64]! == 28)

structure Identity where
  metadataHash : ByteArray
  publicKey : ByteArray
  sender : Nat
  deriving BEq, Inhabited

namespace Identity

def validate (identity : Identity) : Except String Unit := do
  if identity.metadataHash.size != 32 || identity.publicKey.size != 65 ||
      identity.publicKey[0]! != 4 || identity.sender == 0 ||
      identity.sender >= 2 ^ 160 then throw bad

def toJson (identity : Identity) : Json := Json.mkObj [
  ("version", Lean.toJson (1 : Nat)), ("kind", Lean.toJson ("ephemeral-identity" : String)),
  ("metadataHash", hexJson identity.metadataHash), ("publicKey", hexJson identity.publicKey),
  ("sender", Lean.toJson (toString identity.sender))]

def encode (identity : Identity) : String := identity.toJson.compress

private def decodeCore (raw : String) : Except String Identity := do
  if raw.utf8ByteSize > 1024 then throw bad
  let json ← Json.parse raw
  checkHeader json "ephemeral-identity"
  let identity : Identity := {
    metadataHash := ← bytesField json "metadataHash" 32
    publicKey := ← bytesField json "publicKey" 65, sender := ← numberField json "sender" }
  identity.validate
  if identity.encode != raw then throw bad
  return identity

def decode (raw : String) : Except String Identity :=
  (decodeCore raw).mapError (fun _ => bad)

end Identity

structure SignRequest where
  metadata : Metadata
  expectedSender : Nat
  operationHash : ByteArray
  deriving BEq, Inhabited

namespace SignRequest

def validate (request : SignRequest) : Except String Unit := do
  request.metadata.validate
  if request.expectedSender == 0 || request.expectedSender >= 2 ^ 160 ||
      request.operationHash.size != 32 then throw bad

def authorizationHash (request : SignRequest) : Except String ByteArray := do
  request.validate
  Rlp.authorizationHash7702 request.metadata.chainId delegate 0

def toJson (request : SignRequest) : Json := Json.mkObj [
  ("version", Lean.toJson (1 : Nat)), ("kind", Lean.toJson ("ephemeral-sign-request" : String)),
  ("metadata", request.metadata.toJson),
  ("expectedSender", Lean.toJson (toString request.expectedSender)),
  ("operationHash", hexJson request.operationHash)]

def encode (request : SignRequest) : String := request.toJson.compress
def hash (request : SignRequest) : ByteArray := keccak256 request.encode.toUTF8

private def decodeCore (raw : String) : Except String SignRequest := do
  if raw.utf8ByteSize > 3072 then throw bad
  let json ← Json.parse raw
  checkHeader json "ephemeral-sign-request"
  let request : SignRequest := {
    metadata := ← Metadata.decode (← json.getObjVal? "metadata").compress,
    expectedSender := ← numberField json "expectedSender",
    operationHash := ← bytesField json "operationHash" 32 }
  request.validate
  if request.encode != raw then throw bad
  return request

def decode (raw : String) : Except String SignRequest :=
  (decodeCore raw).mapError (fun _ => bad)

end SignRequest

structure SignedResult where
  requestHash : ByteArray
  identity : Identity
  operationSignature : ByteArray
  authorizationSignature : ByteArray
  deriving BEq, Inhabited

namespace SignedResult

def validateFor (request : SignRequest) (result : SignedResult) : Except String Unit := do
  request.validate
  result.identity.validate
  if result.requestHash != request.hash ||
      result.identity.metadataHash != metadataHash request.metadata ||
      result.identity.sender != request.expectedSender ||
      !canonicalSignature result.operationSignature ||
      !canonicalSignature result.authorizationSignature then throw bad

def toJson (result : SignedResult) : Json := Json.mkObj [
  ("version", Lean.toJson (1 : Nat)), ("kind", Lean.toJson ("ephemeral-sign-result" : String)),
  ("requestHash", hexJson result.requestHash), ("identity", result.identity.toJson),
  ("operationSignature", hexJson result.operationSignature),
  ("authorizationSignature", hexJson result.authorizationSignature)]

def encode (result : SignedResult) : String := result.toJson.compress

private def decodeCore (raw : String) : Except String SignedResult := do
  if raw.utf8ByteSize > 2048 then throw bad
  let json ← Json.parse raw
  checkHeader json "ephemeral-sign-result"
  let result : SignedResult := {
    requestHash := ← bytesField json "requestHash" 32,
    identity := ← Identity.decode (← json.getObjVal? "identity").compress,
    operationSignature := ← bytesField json "operationSignature" 65,
    authorizationSignature := ← bytesField json "authorizationSignature" 65 }
  result.identity.validate
  if !canonicalSignature result.operationSignature ||
      !canonicalSignature result.authorizationSignature || result.encode != raw then throw bad
  return result

def decode (raw : String) : Except String SignedResult :=
  (decodeCore raw).mapError (fun _ => bad)

end SignedResult

end Tornado.Protocol.ProverSignerWire
