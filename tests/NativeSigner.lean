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

private def fails (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def word (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

def main (args : List String) : IO UInt32 := do
  let some dir := args.head?
    | throw <| IO.userError "Native signer test requires an absolute private directory."
  let path := dir ++ "/public-test-key"
  let keyText := "0x" ++ String.ofList (List.replicate 63 '0') ++ "1\n"
  let key ← checked "public fixture key" <| parseHexBytes
    ("0x" ++ String.ofList (List.replicate 63 '0') ++ "1")
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
  require (← fails <| signDigestFromProtectedFile path (ByteArray.empty.push 1))
    "A non-32-byte digest reached the signer."

  let malformedPath := dir ++ "/malformed-key"
  let malformed := "0x123g\n".toUTF8
  createPrivate malformedPath malformed
  require (← fails <| publicKeyFromProtectedFile malformedPath)
    "Malformed protected key passed native public-key derivation."
  require (← fails <| signDigestFromProtectedFile malformedPath signed.signingHash)
    "Malformed protected key passed native signing."
  removePrivateExact malformedPath malformed

  let publicPath := dir ++ "/public-key"
  createPrivate publicPath keyText.toUTF8
  IO.Prim.setAccessRights (System.FilePath.mk publicPath) 420 -- mode 0644
  require (← fails <| publicKeyFromProtectedFile publicPath)
    "Group/world-readable key passed native protected-file checks."
  require (← fails <| signDigestFromProtectedFile publicPath signed.signingHash)
    "Group/world-readable key reached native signing."
  IO.FS.removeFile (System.FilePath.mk publicPath)

  let changedText := "0x" ++ String.ofList (List.replicate 63 '0') ++ "2\n"
  replacePrivate path keyText.toUTF8 changedText.toUTF8
  let (changedSender, _) ← sign1559FromProtectedFile path tx
  require (changedSender != sender) "A replaced key retained the reviewed sender."
  removePrivateExact path changedText.toUTF8
  IO.println "PASS: protected native signer matches Lean and viem public vectors"
  return 0
