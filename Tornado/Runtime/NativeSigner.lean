import Tornado.Protocol.TypedTransaction

/-!
The protected EOA signer boundary and public-only worker verification. Key-file
functions read a protected private key in native code and return only an
uncompressed public key or public signature data to Lean. The pinned C
implementation and libsecp256k1 remain
trusted components; Lean checks the returned public point, address, canonical
signature, and exact transaction serialization before any caller may expose it.
No private-key bytes are represented by a Lean value on this path.
-/

namespace Tornado.Runtime.NativeSigner

open Tornado.Crypto Tornado.Protocol Tornado.Protocol.Rlp

@[extern "tornado_secure_pubkey_from_key_file"]
opaque publicKeyFromProtectedFile (path : @& String) : IO ByteArray

/-- Return `uncompressed_pubkey[65] || r[32] || s[32] || recovery_id[1]`.
    Native code checks the signature against the returned public key. -/
@[extern "tornado_secure_sign_digest_from_key_file"]
opaque signDigestFromProtectedFile (path : @& String)
    (digest : @& ByteArray) : IO ByteArray

/-- Disable process core dumps before the isolated worker reads note secrets.
This does not erase Lean values or make its arithmetic constant-time. -/
@[extern "tornado_worker_disable_core_dumps"]
opaque disableWorkerCoreDumps : IO Unit

/-- Public-only libsecp verification and recovery. Both the ECDSA equation
and recovery-id-selected public key must match the supplied public key. -/
@[extern "tornado_verify_public_digest"]
opaque verifyPublicDigest (publicKey digest signature : @& ByteArray) : IO Bool

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def word (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- Validate the public uncompressed point and derive its Ethereum address. -/
def addressOfPublicKey (key : ByteArray) : Except String Nat := do
  if key.size != 65 || key[0]! != 4 then
    throw "Native signer returned an invalid public key."
  let x := word (key.extract 1 33)
  let y := word (key.extract 33 65)
  let p := secp256k1FieldPrime
  if x >= p || y >= p || y * y % p != (x * x * x + 7) % p then
    throw "Native signer returned an off-curve public key."
  return word ((keccak256 (key.extract 1 65)).extract 12 32)

/-- Read a protected key only inside the native boundary, returning its
    public sender address. The private key never reaches Lean. -/
def addressFromProtectedFile (path : String) : IO Nat := do
  let publicKey ← publicKeyFromProtectedFile path
  checked <| addressOfPublicKey publicKey

/-- Sign a public digest without importing the key into Lean. The native
    boundary verifies and recovers the signature; this wrapper also checks its
    canonical Ethereum shape. Return `r || s || (27 + yParity)`. -/
def signDigest65FromProtectedFile (path : String) (digest : ByteArray) :
    IO (Nat × ByteArray) := do
  if digest.size != 32 then
    throw <| IO.userError "Signing digest must contain exactly 32 bytes."
  let response ← signDigestFromProtectedFile path digest
  if response.size != 130 then
    throw <| IO.userError "Native signer returned an invalid signature length."
  let sender ← checked <| addressOfPublicKey (response.extract 0 65)
  let r := word (response.extract 65 97)
  let s := word (response.extract 97 129)
  let recovery := response[129]!.toNat
  if recovery >= 2 || r == 0 || s == 0 ||
      r >= secp256k1Order || s > secp256k1Order / 2 then
    throw <| IO.userError "Native signer returned a noncanonical signature."
  return (sender, (response.extract 65 129).push (27 + recovery).toUInt8)

/-- Sign the exact Lean-serialized type-2 preimage with the protected key.
    The signer address accompanies the result so an effectful caller can
    compare it to the reviewed sender before journaling or broadcasting. -/
def sign1559FromProtectedFile (path : String) (tx : Transaction1559) :
    IO (Nat × TypedTransaction.SignedTyped) := do
  let digest ← checked <| signingHash1559 tx
  let response ← signDigestFromProtectedFile path digest
  if response.size != 130 then
    throw <| IO.userError "Native signer returned an invalid signature length."
  let sender ← checked <| addressOfPublicKey (response.extract 0 65)
  let r := word (response.extract 65 97)
  let s := word (response.extract 97 129)
  let recovery := response[129]!.toNat
  -- Ethereum type-2 envelopes encode only y parity. A recovery ID with the
  -- overflow bit set cannot be represented by the reviewed transaction.
  if recovery >= 2 || r == 0 || s == 0 ||
      r >= secp256k1Order || s > secp256k1Order / 2 then
    throw <| IO.userError "Native signer returned a noncanonical signature."
  let signature : Signature := ⟨recovery % 2, r, s⟩
  let serialized ← checked <| serialize1559 tx (some signature)
  return (sender, ⟨digest, signature, serialized, keccak256 serialized⟩)

end Tornado.Runtime.NativeSigner
