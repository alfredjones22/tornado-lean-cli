import Tornado.Protocol.Rlp
import Tornado.Crypto.Secp256k1

/-!
Native typed transaction payloads used by the CLI's EOA deposit/recovery path
and the EIP-7702 authorization-list envelope. This code is pure Lean: it does
not query the chain, choose a nonce or fee, persist a journal, or broadcast.
Signing uses the existing variable-time secp256k1 implementation and must not
be used with live secrets until that implementation is hardened.
-/

namespace Tornado.Protocol.TypedTransaction

open Tornado.Crypto
open Tornado.Protocol.Rlp

private def fixedBytes (value count : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:count] do
    result := result.push ((value / 256 ^ (count - 1 - i) % 256).toUInt8)
  return result

/-- An EIP-7702 authorization as it appears inside a type-4 transaction.
    A chain ID of zero is the protocol's wildcard authorization. -/
structure Authorization7702 where
  chainId : Nat
  delegate : Nat
  nonce : Nat
  signature : Signature
  deriving Inhabited

/-- The type-4 envelope reuses the type-2 fee, recipient and access-list
    fields and appends the authorization list before the transaction signature. -/
structure Transaction7702 where
  base : Transaction1559
  authorizations : Array Authorization7702
  deriving Inhabited

/-- A validated authorization requires protocol-width fields and a canonical
    secp256k1 signature. Viem's serializer can encode invalid signatures; this
    native entry point rejects them before producing transaction bytes. -/
def validateAuthorization (auth : Authorization7702) : Except String Unit := do
  if auth.chainId >= maxUint256 || auth.nonce >= maxUint256 then
    throw "EIP-7702 authorization integer is out of range."
  if auth.delegate >= maxAddress then
    throw "EIP-7702 delegate is outside uint160."
  if auth.signature.yParity > 1 || auth.signature.r == 0 ||
      auth.signature.s == 0 || auth.signature.r >= secp256k1Order ||
      auth.signature.s >= secp256k1Order then
    throw "Invalid EIP-7702 authorization signature."

def validateAuthorizationList (items : Array Authorization7702) : Except String Unit := do
  for item in items do validateAuthorization item

/-- RLP fields for one signed authorization: chain, delegate, nonce, parity,
    r, s. The 20-byte delegate is kept at its fixed address width. -/
def authorizationFields (auth : Authorization7702) : List ByteArray :=
  [nat auth.chainId, bytes (fixedBytes auth.delegate 20), nat auth.nonce,
    nat auth.signature.yParity, nat auth.signature.r, nat auth.signature.s]

/-- The list shape is independent of the byte values, which makes accidental
    omission of an authorization visible at the pure representation boundary. -/
def authorizationItems (items : Array Authorization7702) : List ByteArray :=
  items.toList.map (fun item => list (authorizationFields item))

theorem authorization_items_preserve_count (items : Array Authorization7702) :
    (authorizationItems items).length = items.size := by
  simp [authorizationItems]

private def accessListItems (items : Array AccessEntry) : List ByteArray :=
  items.toList.map fun item =>
    list [bytes (fixedBytes item.address 20),
      list (item.storageKeys.toList.map bytes)]

private def signatureItems (sig : Signature) : Except String (List ByteArray) := do
  if sig.yParity > 1 || sig.r == 0 || sig.s == 0 ||
      sig.r >= secp256k1Order || sig.s >= secp256k1Order then
    throw "Invalid typed transaction signature."
  return [nat sig.yParity, nat sig.r, nat sig.s]

/-- The ten unsigned type-4 fields. The authorization list occupies the
    final field; a transaction signature, when present, is appended after it. -/
def unsignedFields7702 (tx : Transaction7702) : List ByteArray :=
  let recipient := match tx.base.to with
    | none => ByteArray.empty
    | some address => fixedBytes address 20
  [nat tx.base.chainId, nat tx.base.nonce,
    nat tx.base.maxPriorityFeePerGas, nat tx.base.maxFeePerGas,
    nat tx.base.gas, bytes recipient, nat tx.base.value,
    bytes tx.base.data, list (accessListItems tx.base.accessList),
    list (authorizationItems tx.authorizations)]

theorem unsigned_fields_include_authorizations (tx : Transaction7702) :
    (unsignedFields7702 tx)[9]? =
      some (list (authorizationItems tx.authorizations)) := by
  simp [unsignedFields7702]

/-- Type-4 transaction serialization: 0x04 || RLP([chainId, nonce, fees,
    gas, to, value, data, accessList, authorizationList, signature?]). -/
def serialize7702 (tx : Transaction7702)
    (signature : Option Signature := none) : Except String ByteArray := do
  validateTransaction tx.base
  validateAuthorizationList tx.authorizations
  let suffix ← match signature with
    | none => pure []
    | some sig => signatureItems sig
  return (ByteArray.empty.push 0x04) ++ list (unsignedFields7702 tx ++ suffix)

def signingHash7702 (tx : Transaction7702) : Except String ByteArray :=
  (serialize7702 tx none).map keccak256

def transactionHash7702 (tx : Transaction7702)
    (signature : Signature) : Except String ByteArray :=
  (serialize7702 tx (some signature)).map keccak256

/-- The exact signed bytes and their preimage/hash for review and durable
    reservation. The caller must persist a reservation before exposure. -/
structure SignedTyped where
  signingHash : ByteArray
  signature : Signature
  serialized : ByteArray
  transactionHash : ByteArray

private def ecdsaSignature (sig : SecpSignature) : Signature :=
  { yParity := sig.recovery % 2, r := sig.r, s := sig.s }

/-- Sign the EIP-7702 authorization hash using the native Lean signer. The
    result is purely in memory; an effectful caller must reserve its use and
    must never leak it through estimation without a durable recovery record. -/
def signAuthorization7702 (chainId delegate nonce : Nat)
    (privateKey : ByteArray) : Except String Authorization7702 := do
  let digest ← authorizationHash7702 chainId delegate nonce
  let signature := ecdsaSignature (← secp256k1SignDigest privateKey digest)
  let authorization : Authorization7702 := ⟨chainId, delegate, nonce, signature⟩
  validateAuthorization authorization
  return authorization

/-- Deterministically sign a type-2 transaction with the native Lean signer.
    This pure compatibility routine does not use the protected key-file signer. -/
def sign1559 (tx : Transaction1559) (privateKey : ByteArray) : Except String SignedTyped := do
  let signingHash ← signingHash1559 tx
  let signature := ecdsaSignature (← secp256k1SignDigest privateKey signingHash)
  let serialized ← serialize1559 tx (some signature)
  return ⟨signingHash, signature, serialized, keccak256 serialized⟩

/-- Deterministically sign a type-4 transaction with the native Lean signer. -/
def sign7702 (tx : Transaction7702) (privateKey : ByteArray) : Except String SignedTyped := do
  let signingHash ← signingHash7702 tx
  let signature := ecdsaSignature (← secp256k1SignDigest privateKey signingHash)
  let serialized ← serialize7702 tx (some signature)
  return ⟨signingHash, signature, serialized, keccak256 serialized⟩

/-- A type-4 signing payload cannot be produced with a zero transaction
    chain ID, even though individual authorizations may use wildcard zero. -/
theorem zero_transaction_chain_rejected (tx : Transaction7702)
    (h : tx.base.chainId = 0) : (serialize7702 tx none).isOk = false := by
  simp [serialize7702, validateTransaction, h, bind, Except.bind]
  rfl

/-- The type-4 encoder cannot return bytes until the entire supplied
    authorization list has passed native width and signature checks. -/
theorem serialization_requires_valid_authorizations (tx : Transaction7702)
    (signature : Option Signature) (raw : ByteArray)
    (h : serialize7702 tx signature = .ok raw) :
    validateAuthorizationList tx.authorizations = .ok () := by
  cases ht : validateTransaction tx.base with
  | error _ => simp [serialize7702, bind, Except.bind, ht] at h
  | ok _ =>
    cases ha : validateAuthorizationList tx.authorizations with
    | error _ => simp [serialize7702, bind, Except.bind, ht, ha] at h
    | ok value =>
      cases value
      rfl

/-- Invalid standalone authorization addresses are rejected before any
    authorization-list serialization. -/
theorem invalid_delegate_rejected (auth : Authorization7702)
    (h : auth.delegate >= maxAddress) :
    (validateAuthorization auth).isOk = false := by
  by_cases hi : auth.chainId >= maxUint256 || auth.nonce >= maxUint256
  · simp [validateAuthorization, hi, bind, Except.bind]
    rfl
  · simp [validateAuthorization, hi, h, bind, Except.bind]
    rfl

/-- An accepted native authorization signs precisely the supplied chain,
    delegate and nonce tuple and has passed the canonical field guards. -/
theorem signed_authorization_binds_fields (chainId delegate nonce : Nat)
    (privateKey : ByteArray) (auth : Authorization7702)
    (h : signAuthorization7702 chainId delegate nonce privateKey = .ok auth) :
    auth.chainId = chainId ∧ auth.delegate = delegate ∧ auth.nonce = nonce ∧
      validateAuthorization auth = .ok () := by
  unfold signAuthorization7702 at h
  cases hd : authorizationHash7702 chainId delegate nonce with
  | error _ => simp [bind, Except.bind, hd] at h
  | ok digest =>
    cases hs : secp256k1SignDigest privateKey digest with
    | error _ => simp [bind, Except.bind, hd, hs] at h
    | ok signed =>
      let candidate : Authorization7702 :=
        ⟨chainId, delegate, nonce, ecdsaSignature signed⟩
      cases hv : validateAuthorization candidate with
      | error _ => simp [bind, Except.bind, hd, hs, candidate, hv] at h
      | ok _ =>
        simp [bind, Except.bind, hd, hs, candidate, hv] at h
        cases h
        exact ⟨rfl, rfl, rfl, hv⟩

/-- Every returned signed type-4 hash is the hash of the exact bytes that
    the native serializer produced. This does not prove ECDSA security or the
    truth of network-supplied nonce, fee, or chain state. -/
theorem sign7702_hashes_serialized_bytes (tx : Transaction7702)
    (privateKey : ByteArray) (result : SignedTyped)
    (h : sign7702 tx privateKey = .ok result) :
    result.transactionHash = keccak256 result.serialized := by
  cases hsign : signingHash7702 tx with
  | error _ => simp [sign7702, bind, Except.bind, hsign] at h
  | ok digest =>
    cases hkey : secp256k1SignDigest privateKey digest with
    | error _ => simp [sign7702, bind, Except.bind, hsign, hkey] at h
    | ok sig =>
      cases hraw : serialize7702 tx (some (ecdsaSignature sig)) with
      | error _ => simp [sign7702, bind, Except.bind, hsign, hkey, hraw] at h
      | ok raw =>
        simp [sign7702, bind, Except.bind, hsign, hkey, hraw] at h
        cases h
        rfl

/-- The same serialization-to-hash relation holds for native type-2 signing. -/
theorem sign1559_hashes_serialized_bytes (tx : Transaction1559)
    (privateKey : ByteArray) (result : SignedTyped)
    (h : sign1559 tx privateKey = .ok result) :
    result.transactionHash = keccak256 result.serialized := by
  cases hsign : signingHash1559 tx with
  | error _ => simp [sign1559, bind, Except.bind, hsign] at h
  | ok digest =>
    cases hkey : secp256k1SignDigest privateKey digest with
    | error _ => simp [sign1559, bind, Except.bind, hsign, hkey] at h
    | ok sig =>
      cases hraw : serialize1559 tx (some (ecdsaSignature sig)) with
      | error _ => simp [sign1559, bind, Except.bind, hsign, hkey, hraw] at h
      | ok raw =>
        simp [sign1559, bind, Except.bind, hsign, hkey, hraw] at h
        cases h
        rfl

end Tornado.Protocol.TypedTransaction

#print axioms Tornado.Protocol.TypedTransaction.authorization_items_preserve_count
#print axioms Tornado.Protocol.TypedTransaction.unsigned_fields_include_authorizations
#print axioms Tornado.Protocol.TypedTransaction.zero_transaction_chain_rejected
#print axioms Tornado.Protocol.TypedTransaction.serialization_requires_valid_authorizations
#print axioms Tornado.Protocol.TypedTransaction.invalid_delegate_rejected
#print axioms Tornado.Protocol.TypedTransaction.signed_authorization_binds_fields
#print axioms Tornado.Protocol.TypedTransaction.sign7702_hashes_serialized_bytes
#print axioms Tornado.Protocol.TypedTransaction.sign1559_hashes_serialized_bytes
