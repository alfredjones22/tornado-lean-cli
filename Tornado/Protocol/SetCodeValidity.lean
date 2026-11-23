import Tornado.Protocol.TypedTransaction

/-!
A separate, pure admission gate for signed EIP-7702 type-4 transactions. The
`TypedTransaction` encoder intentionally retains viem's raw serialization
surface, including inputs which the protocol would reject. This module checks
stateless consensus conditions and, separately, whether every authorization
is eligible to take effect. It neither proves that an authorization signature
recovers the intended account nor checks on-chain account state.
-/

namespace Tornado.Protocol.SetCodeValidity

open Tornado.Crypto
open Tornado.Protocol.Rlp
open Tornado.Protocol.TypedTransaction

/-- EIP-7702 inherits EIP-2930's intrinsic cost and adds 25,000 per
    authorization, even if that authorization is ultimately skipped. -/
def intrinsicGas7702 (tx : Transaction7702) : Nat :=
  let calldata := tx.base.data.data.foldl
    (fun total byte => total + if byte == 0 then 4 else 16) 0
  let access := tx.base.accessList.toList.foldl
    (fun total entry => total + 2400 + 1900 * entry.storageKeys.size) 0
  21000 + calldata + access + 25000 * tx.authorizations.size

/-- The exact width check that invalidates an entire transaction. A nonce of
    `2^64 - 1` fits the tuple and does not invalidate the envelope, but the
    protocol will skip that individual authorization during processing. -/
def authorizationFits7702 (auth : Authorization7702) : Bool :=
  auth.nonce < 2 ^ 64

/-- Stateless checks for a signed type-4 envelope. The raw validators are
    applied separately by `validateSetCodeEnvelope`. -/
def envelopeFields7702 (tx : Transaction7702) (sig : Signature) : Bool :=
  tx.base.to.isSome &&
  !tx.authorizations.isEmpty &&
  tx.authorizations.all authorizationFits7702 &&
  intrinsicGas7702 tx <= tx.base.gas &&
  sig.s <= secp256k1Order / 2

/-- Reject type-4 envelopes that fail stateless protocol requirements:
    recipient, nonempty authorizations, tuple nonce width, intrinsic gas,
    and EIP-2 low-S outer signature. The base/raw validators also check
    field widths, fee ordering, access-list shape, and signature scalars. -/
def validateSetCodeEnvelope (tx : Transaction7702)
    (sig : Signature) : Except String Unit := do
  validateTransaction tx.base
  validateAuthorizationList tx.authorizations
  if sig.yParity > 1 || sig.r == 0 || sig.s == 0 ||
      sig.r >= secp256k1Order || sig.s >= secp256k1Order then
    throw "Invalid type-4 transaction signature."
  else
    if envelopeFields7702 tx sig then
      return ()
    else
      throw "Invalid EIP-7702 envelope: destination, authorization list, nonce width, intrinsic gas, or low-S signature."

/-- A tuple that passes these additional checks is not skipped for its
    *stateless* chain/nonce/signature conditions. The protocol can still skip
    it after checking recovered signer, account code, and account nonce. -/
def authorizationStatelesslyEffective (chainId : Nat)
    (auth : Authorization7702) : Bool :=
  (auth.chainId == 0 || auth.chainId == chainId) &&
  auth.nonce < 2 ^ 64 - 1 &&
  auth.signature.s <= secp256k1Order / 2

/-- CLI intent gate: every listed authorization must be eligible to take
    effect under the stateless EIP-7702 processing rules. A skipped tuple
    still leaves the envelope consensus-valid, but is unsafe to treat as an
    applied delegation. -/
def validateSetCodeIntent (tx : Transaction7702)
    (sig : Signature) : Except String Unit := do
  validateSetCodeEnvelope tx sig
  if tx.authorizations.all
      (authorizationStatelesslyEffective tx.base.chainId) = true then
    return ()
  else
    throw "An EIP-7702 authorization would be skipped by stateless protocol checks."

/-- Retain the native raw serializer byte-for-byte; strict admission is a
    separate check before returning signed bytes. -/
def serializeSetCodeIntent (tx : Transaction7702)
    (sig : Signature) : Except String ByteArray := do
  validateSetCodeIntent tx sig
  serialize7702 tx (some sig)

theorem accepted_envelope_satisfies_shape (tx : Transaction7702)
    (sig : Signature)
    (h : validateSetCodeEnvelope tx sig = .ok ()) :
    envelopeFields7702 tx sig = true := by
  unfold validateSetCodeEnvelope at h
  cases ht : validateTransaction tx.base with
  | error _ => simp [bind, Except.bind, ht] at h
  | ok _ =>
    cases ha : validateAuthorizationList tx.authorizations with
    | error _ => simp [bind, Except.bind, ht, ha] at h
    | ok _ =>
      by_cases hs : sig.yParity > 1 || sig.r == 0 || sig.s == 0 ||
          sig.r >= secp256k1Order || sig.s >= secp256k1Order
      · simp [bind, Except.bind, ht, ha, hs] at h
      · simp [bind, Except.bind, ht, ha, hs] at h
        cases hf : envelopeFields7702 tx sig with
        | false => simp [hf] at h
        | true => rfl

theorem accepted_envelope_has_destination (tx : Transaction7702)
    (sig : Signature)
    (h : validateSetCodeEnvelope tx sig = .ok ()) :
    tx.base.to.isSome = true := by
  have hs := accepted_envelope_satisfies_shape tx sig h
  simp only [envelopeFields7702, Bool.and_eq_true] at hs
  exact hs.1.1.1.1

theorem accepted_envelope_has_authorizations (tx : Transaction7702)
    (sig : Signature)
    (h : validateSetCodeEnvelope tx sig = .ok ()) :
    tx.authorizations.isEmpty = false := by
  have hs := accepted_envelope_satisfies_shape tx sig h
  simp only [envelopeFields7702, Bool.and_eq_true] at hs
  cases he : tx.authorizations.isEmpty with
  | false => rfl
  | true => simp [he] at hs

theorem accepted_envelope_covers_intrinsic_gas (tx : Transaction7702)
    (sig : Signature)
    (h : validateSetCodeEnvelope tx sig = .ok ()) :
    intrinsicGas7702 tx <= tx.base.gas := by
  have hs := accepted_envelope_satisfies_shape tx sig h
  simp only [envelopeFields7702, Bool.and_eq_true] at hs
  simpa using hs.1.2

theorem accepted_envelope_has_low_s (tx : Transaction7702)
    (sig : Signature)
    (h : validateSetCodeEnvelope tx sig = .ok ()) :
    sig.s <= secp256k1Order / 2 := by
  have hs := accepted_envelope_satisfies_shape tx sig h
  simp only [envelopeFields7702, Bool.and_eq_true] at hs
  simpa using hs.2

theorem accepted_envelope_auth_nonce_fits (tx : Transaction7702)
    (sig : Signature) (i : Nat) (hi : i < tx.authorizations.size)
    (h : validateSetCodeEnvelope tx sig = .ok ()) :
    tx.authorizations[i].nonce < 2 ^ 64 := by
  have hs := accepted_envelope_satisfies_shape tx sig h
  simp only [envelopeFields7702, Bool.and_eq_true] at hs
  have hitem := Array.all_eq_true.mp hs.1.1.2 i hi
  simpa [authorizationFits7702] using hitem

theorem accepted_intent_has_effective_fields (tx : Transaction7702)
    (sig : Signature)
    (h : validateSetCodeIntent tx sig = .ok ()) :
    tx.authorizations.all
      (authorizationStatelesslyEffective tx.base.chainId) = true := by
  unfold validateSetCodeIntent at h
  cases hv : validateSetCodeEnvelope tx sig with
  | error _ => simp [bind, Except.bind, hv] at h
  | ok _ =>
    simp [bind, Except.bind, hv] at h
    cases ha : tx.authorizations.all
      (authorizationStatelesslyEffective tx.base.chainId) with
    | false =>
      have hnot : ¬∀ (i : Nat) (hi : i < tx.authorizations.size),
          authorizationStatelesslyEffective tx.base.chainId
            tx.authorizations[i] = true := by
        intro hforall
        have htrue : tx.authorizations.all
            (authorizationStatelesslyEffective tx.base.chainId) = true :=
          Array.all_eq_true.mpr hforall
        simp [ha] at htrue
      simp [hnot] at h
    | true => rfl

theorem accepted_intent_auth_nonce_is_processable (tx : Transaction7702)
    (sig : Signature) (i : Nat) (hi : i < tx.authorizations.size)
    (h : validateSetCodeIntent tx sig = .ok ()) :
    tx.authorizations[i].nonce < 2 ^ 64 - 1 := by
  have hs := accepted_intent_has_effective_fields tx sig h
  have hitem := Array.all_eq_true.mp hs i hi
  simp only [authorizationStatelesslyEffective, Bool.and_eq_true] at hitem
  simpa using hitem.1.2

theorem accepted_serialization_is_raw_serialization (tx : Transaction7702)
    (sig : Signature) (raw : ByteArray)
    (h : serializeSetCodeIntent tx sig = .ok raw) :
    serialize7702 tx (some sig) = .ok raw := by
  unfold serializeSetCodeIntent at h
  cases hv : validateSetCodeIntent tx sig with
  | error _ => simp [bind, Except.bind, hv] at h
  | ok _ => simpa [bind, Except.bind, hv] using h

end Tornado.Protocol.SetCodeValidity

#print axioms Tornado.Protocol.SetCodeValidity.accepted_envelope_satisfies_shape
#print axioms Tornado.Protocol.SetCodeValidity.accepted_envelope_has_destination
#print axioms Tornado.Protocol.SetCodeValidity.accepted_envelope_has_authorizations
#print axioms Tornado.Protocol.SetCodeValidity.accepted_envelope_covers_intrinsic_gas
#print axioms Tornado.Protocol.SetCodeValidity.accepted_envelope_has_low_s
#print axioms Tornado.Protocol.SetCodeValidity.accepted_envelope_auth_nonce_fits
#print axioms Tornado.Protocol.SetCodeValidity.accepted_intent_has_effective_fields
#print axioms Tornado.Protocol.SetCodeValidity.accepted_intent_auth_nonce_is_processable
#print axioms Tornado.Protocol.SetCodeValidity.accepted_serialization_is_raw_serialization
