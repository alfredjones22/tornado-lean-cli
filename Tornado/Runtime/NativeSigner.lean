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

/-- Read directly from a no-echo controlling terminal into locked native
memory. The returned command-local alias is public and is not a disk file. -/
@[extern "tornado_secure_prompt_key"]
opaque promptKey (anchor : @& String) : IO String

@[extern "tornado_secure_clear_prompt_key"]
opaque clearPromptKey : IO Unit

/-- Classify a protected raw key or unlock a Web3 Secret Storage v3 keystore.
The native boundary retains decrypted keys in its command-local session and
returns only the original public source path. Mode bits select a password
file and non-interactive policy; password contents remain native. -/
@[extern "tornado_secure_unlock_key_file"]
opaque unlockKeyFile (path passwordFile : @& String) (mode : UInt32) : IO String

/-- Only a password-file path and prompt policy cross the Lean boundary.
Password contents are read by native code, never represented as Lean values. -/
structure PasswordOptions where
  passwordFile : Option String := none
  nonInteractive : Bool := false
  deriving Inhabited

def PasswordOptions.hasSource (options : PasswordOptions) : Bool :=
  options.passwordFile.isSome

def PasswordOptions.withPasswordFile (options : PasswordOptions) (value : String) :
    Except String PasswordOptions := do
  if options.hasSource then throw "Use only one --pwd-file option."
  if value.isEmpty then throw "Provide a nonempty --pwd-file path."
  return { options with passwordFile := some value }

/-- Mode/help dispatch must not mistake a password-file path such as
`--broadcast` or `--help` for a control flag. Parsers use the original arguments. -/
def withoutPasswordArguments : List String → List String
  | [] => []
  | "--pwd-file" :: _ :: rest => withoutPasswordArguments rest
  | value :: rest =>
    if value.startsWith "--pwd-file=" then
      withoutPasswordArguments rest
    else value :: withoutPasswordArguments rest

/-- File arguments remain optional at the CLI boundary. Interactive sources
use the journal directory for durable claims, or the home directory otherwise.
No private key or terminal input is represented by a Lean value. -/
def resolveKeyFile (file : Option String) (journal : Option String := none)
    (passwords : PasswordOptions := {}) : IO String := do
  let current ← IO.currentDir
  let absolute (path : String) :=
    if (System.FilePath.mk path).isAbsolute then path else (current / path).toString
  if let some path := file then
    if path.isEmpty then throw <| IO.userError "Provide a nonempty account key-file path."
    let mode : UInt32 := (if passwords.passwordFile.isSome then 2 else 0) +
      (if passwords.nonInteractive then 4 else 0)
    return ← unlockKeyFile (absolute path) (passwords.passwordFile.map absolute |>.getD "") mode
  if passwords.hasSource then
    throw <| IO.userError "--pwd-file requires --key-file or --owner-key-file."
  if passwords.nonInteractive then
    throw <| IO.userError "--non-interactive requires an account key file; hidden key entry is unavailable."
  let directory ← match journal with
    | some path => do
      let absolute := if (System.FilePath.mk path).isAbsolute then System.FilePath.mk path
        else current / path
      let some parent := absolute.parent
        | throw <| IO.userError "Journal has no signing directory."
      pure parent
    | none => do
      let some homeDirectory ← IO.getEnv "HOME"
        | throw <| IO.userError "Provide a key file when no home directory is configured."
      pure (System.FilePath.mk homeDirectory)
  let parent := directory.toString
  promptKey (parent ++ (if parent.endsWith "/" then "" else "/") ++ ".tornado-interactive-key-")

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
