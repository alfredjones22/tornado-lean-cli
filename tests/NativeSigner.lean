import Tornado.Runtime.NativeSigner
import Tornado.Runtime.ProtectedIO
import Tornado.Domain.NoteIdentity

/-! Public, unfunded fixture for the protected native secp256k1 boundary. -/

open Tornado.Crypto Tornado.Domain Tornado.Protocol.Rlp
open Tornado.Protocol.TypedTransaction
open Tornado.Runtime.NativeSigner Tornado.Runtime.ProtectedIO

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def checked (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def expectDiagnostic (label expected path : String)
    (action : IO α) (forbidden : String := "") : IO Unit := do
  let result ← try
    let _ ← action
    pure (none : Option String)
  catch error => pure (some error.toString)
  let some message := result
    | throw <| IO.userError s!"{label} unexpectedly succeeded."
  require ((message.splitOn expected).length > 1 &&
    (message.splitOn path).length == 1 &&
    (forbidden.isEmpty || (message.splitOn forbidden).length == 1))
    s!"{label} did not return a fixed, private diagnostic."

private def expectKeyDiagnostic (label expected path : String)
    (digest : ByteArray) (forbidden : String := "") : IO Unit := do
  expectDiagnostic (label ++ " public key") expected path
    (publicKeyFromProtectedFile path) forbidden
  expectDiagnostic (label ++ " signature") expected path
    (signDigestFromProtectedFile path digest) forbidden

private def linked (args : Array String) : IO Unit := do
  let result ← IO.Process.output { cmd := "/bin/ln", args }
  require (result.exitCode == 0) "Could not create synthetic key-file link."

private def word (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def fails (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def natBytes (value count : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn fun index : Fin count =>
    UInt8.ofNat (value / 256 ^ (count - 1 - index.val) % 256))

def main (args : List String) : IO UInt32 := do
  let some dir := args.head?
    | throw <| IO.userError "Native signer test requires an absolute private directory."
  let path := dir ++ "/public-test-key"
  let keyText := "0x" ++ String.ofList (List.replicate 63 '0') ++ "1\n"
  let key ← checked "public fixture key" <| parseHexBytes
    ("0x" ++ String.ofList (List.replicate 63 '0') ++ "1")
  if args[1]? == some "interactive" then
    let result ← try
      try
        let source ← promptKey (dir ++ "/.tornado-interactive-key-")
        require (!(← (System.FilePath.mk source).pathExists)) "Interactive key was persisted to disk."
        let pubkey ← publicKeyFromProtectedFile source
        let expected ← checked "public key fixture" <| secp256k1PublicKey key
        require (pubkey == expected) "Interactive signer returned another key."
        let digest := natBytes 42 32
        let (_, signature) ← signDigest65FromProtectedFile source digest
        require (← verifyPublicDigest pubkey digest signature) "Interactive signature failed public verification."
        IO.println "INTERACTIVE_READY_FOR_APPROVAL"
        require ((← (← IO.getStdin).getLine).trimAscii.toString == "APPROVE")
          "Pasted typeahead reached a later approval."
        clearPromptKey
        require (← fails <| publicKeyFromProtectedFile source) "Closed interactive key stayed usable."
        IO.println "PASS: hidden native key input, public signature, no disk key, typeahead isolation and cleanup"
        pure (0 : UInt32)
      finally clearPromptKey
    catch error =>
      IO.eprintln error.toString
      pure (1 : UInt32)
    IO.println s!"INTERACTIVE_EXIT_CODE:{result}"
    -- Keep the controlling session alive while the parent verifies termios.
    let _ ← (← IO.getStdin).getLine
    return result
  createPrivate path keyText.toUTF8

  let expectedPub ← checked "reference public key" <| secp256k1PublicKey key
  let actualPub ← publicKeyFromProtectedFile path
  require (actualPub == expectedPub) "Native public key differs from the Lean reference."
  let expectedAddress ← checked "reference address" <| secp256k1EthereumAddress key
  let sender ← addressFromProtectedFile path
  require (sender == word expectedAddress) "Native sender differs from the Lean reference."
  let unicodePath := dir ++ "/unicode-whitespace-key"
  let unicodeKey := ByteArray.mk #[0xef, 0xbb, 0xbf, 0x09] ++
    ("0x" ++ String.ofList (List.replicate 63 '0') ++ "1").toUTF8 ++
    ByteArray.mk #[0xc2, 0xa0, 0xe3, 0x80, 0x80]
  createPrivate unicodePath unicodeKey
  require ((← addressFromProtectedFile unicodePath) == sender)
    "Native key parser changed JavaScript whitespace behavior."
  removePrivateExact unicodePath unicodeKey
  require (!(addressOfPublicKey (ByteArray.mk (Array.replicate 65 0))).isOk)
    "Malformed public key passed the Lean gate."

  let tx : Transaction1559 :=
    ⟨1, 0, 1000000000, 2000000000, 21000,
     some 0x1111111111111111111111111111111111111111,
     0, ByteArray.empty, #[]⟩
  let (signedSender, signed) ← sign1559FromProtectedFile path tx
  let reference ← checked "reference EIP-1559 signer" <| sign1559 tx key
  require (signedSender == sender && signed.signingHash == reference.signingHash &&
    signed.serialized == reference.serialized &&
    signed.transactionHash == reference.transactionHash)
    "Native EIP-1559 signature differs from the Lean reference."
  let (digestSender, digestSignature) ← signDigest65FromProtectedFile path signed.signingHash
  let expectedSignature ← checked "reference digest signature" <|
    secp256k1SignDigest key signed.signingHash
  require (digestSender == sender && digestSignature == expectedSignature.bytes65)
    "Protected digest signature differs from the independent Lean reference."
  require ("0x" ++ bytesToHex signed.serialized ==
    "0x02f86a0180843b9aca0084773594008252089411111111111111111111111111111111111111118080c080a0aec276508dbbf543a32c80655015b43c4158c2f3ea92511db73306ea9b94a6a0a0159830c5daff66c7ebc21d08357ad74853ca2b7f3edaac1655790561a5e514ee")
    "Native EIP-1559 bytes differ from the pinned viem oracle."
  expectDiagnostic "short digest"
    "Protected signer requires an exact 32-byte digest." path
    (signDigestFromProtectedFile path (ByteArray.empty.push 1))

  let malformedPath := dir ++ "/malformed-key"
  let malformed := "0x123g\n".toUTF8
  createPrivate malformedPath malformed
  expectKeyDiagnostic "malformed key"
    "Protected key file must contain one 0x-prefixed 32-byte hex key. Use a raw key file, not an encrypted JSON keystore."
    malformedPath signed.signingHash
  removePrivateExact malformedPath malformed

  let sentinelPath := dir ++ "/sentinel-key"
  let sentinel := "SYNTHETIC_KEY_SENTINEL_MUST_NOT_APPEAR_IN_ERRORS\n"
  createPrivate sentinelPath sentinel.toUTF8
  expectKeyDiagnostic "sentinel key"
    "Protected key file must contain one 0x-prefixed 32-byte hex key. Use a raw key file, not an encrypted JSON keystore."
    sentinelPath signed.signingHash "SYNTHETIC_KEY_SENTINEL_MUST_NOT_APPEAR_IN_ERRORS"
  removePrivateExact sentinelPath sentinel.toUTF8

  let zeroPath := dir ++ "/zero-key"
  let zero := "0x" ++ String.ofList (List.replicate 64 '0') ++ "\n"
  createPrivate zeroPath zero.toUTF8
  expectKeyDiagnostic "zero scalar"
    "Protected key is not a valid secp256k1 scalar."
    zeroPath signed.signingHash
  removePrivateExact zeroPath zero.toUTF8

  let orderPath := dir ++ "/order-key"
  let order := "0x" ++ bytesToHex (natBytes secp256k1Order 32) ++ "\n"
  createPrivate orderPath order.toUTF8
  expectKeyDiagnostic "out-of-range scalar"
    "Protected key is not a valid secp256k1 scalar."
    orderPath signed.signingHash
  removePrivateExact orderPath order.toUTF8

  let missingPath := dir ++ "/missing-key"
  expectKeyDiagnostic "missing key"
    "Protected key file is missing. Check the key-file path."
    missingPath signed.signingHash

  let symlinkPath := dir ++ "/symlink-key"
  linked #["-s", path, symlinkPath]
  expectKeyDiagnostic "symbolic-link key"
    "Protected key path contains a symbolic link."
    symlinkPath signed.signingHash
  IO.FS.removeFile (System.FilePath.mk symlinkPath)

  let hardlinkPath := dir ++ "/hardlink-key"
  linked #[path, hardlinkPath]
  expectKeyDiagnostic "hard-linked key"
    "Protected key file must have exactly one hard link."
    hardlinkPath signed.signingHash
  IO.FS.removeFile (System.FilePath.mk hardlinkPath)

  let oversizedPath := dir ++ "/oversized-key"
  let oversized := ByteArray.mk (Array.replicate 1025 (0x41 : UInt8))
  createPrivate oversizedPath oversized
  expectKeyDiagnostic "oversized key"
    "Protected key file exceeds the 1024-byte limit."
    oversizedPath signed.signingHash
  removePrivateExact oversizedPath oversized

  let directoryPath := dir ++ "/directory-key"
  IO.FS.createDir directoryPath
  expectKeyDiagnostic "directory instead of key"
    "Protected key file must be a regular file."
    directoryPath signed.signingHash
  IO.FS.removeDir directoryPath

  let publicPath := dir ++ "/public-key"
  createPrivate publicPath keyText.toUTF8
  IO.Prim.setAccessRights (System.FilePath.mk publicPath) 420 -- mode 0644
  expectKeyDiagnostic "0644 key"
    "Protected key file permissions must exclude group/other access and special bits. Use chmod 600 on the key file."
    publicPath signed.signingHash
  IO.FS.removeFile (System.FilePath.mk publicPath)

  if System.Platform.isOSX then
    let aclPath := dir ++ "/acl-key"
    createPrivate aclPath keyText.toUTF8
    let grant ← IO.Process.output {
      cmd := "/bin/chmod"
      args := #["+a", "everyone allow read", aclPath] }
    require (grant.exitCode == 0) "Could not set synthetic key-file ACL."
    expectKeyDiagnostic "ACL-granted key"
      "Protected key file ACL policy could not be verified."
      aclPath signed.signingHash
    IO.FS.removeFile (System.FilePath.mk aclPath)

  let changedText := "0x" ++ String.ofList (List.replicate 63 '0') ++ "2\n"
  replacePrivate path keyText.toUTF8 changedText.toUTF8
  let (changedSender, _) ← sign1559FromProtectedFile path tx
  require (changedSender != sender) "A replaced key retained the reviewed sender."
  removePrivateExact path changedText.toUTF8
  IO.println "PASS: protected native signer matches Lean and viem public vectors"
  return 0
