import Tornado.Runtime.NativeSigner
import Tornado.Runtime.ProtectedIO
import Tornado.Domain.NoteIdentity

/-! Test-only native keystore driver. All keys used by its caller are public,
unfunded fixture keys. No network or transaction submission is implemented. -/

open Tornado.Crypto Tornado.Domain Tornado.Runtime.NativeSigner Tornado.Runtime.ProtectedIO

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

private def fixtureKey (name : String) : IO ByteArray :=
  checked <| parseHexBytes <| if name == "official" then
    "0x7a28b5ba57c53603b0b07b56bba752f7784bf506fa95edc395f5cf6c7514fe9d"
  else if name == "geth31" then
    "0x00fa7b3db73dc7dfdf8c5fbdb796d741e4488628c41fc4febd9160a866ba0f35"
  else if name == "geth30" then
    "0x000081c29e8142bb6a81bef5a92bda7a8328a5c85bb2f9542e76f9b0f94fc018"
  else if name == "two" then
    "0x" ++ String.ofList (List.replicate 63 '0') ++ "2"
  else "0x" ++ String.ofList (List.replicate 63 '0') ++ "1"

private def failed (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def checkSource (path expected : String) : IO Unit := do
  let reference ← fixtureKey expected
  let pub ← publicKeyFromProtectedFile path
  require (pub == (← checked <| secp256k1PublicKey reference))
    "Public fixture keystore decrypted to another identity."
  let digest := ByteArray.mk (Array.replicate 31 0) |>.push 42
  let (_, signature) ← signDigest65FromProtectedFile path digest
  let refSignature ← checked <| secp256k1SignDigest reference digest
  require (signature == refSignature.bytes65)
    "Protected keystore signature differs from the independent Lean fixture."
  require (← verifyPublicDigest pub digest signature)
    "Protected keystore signature failed public verification."

private def probe (path passwordFile modeText expected : String) : IO Unit := do
  let some mode := modeText.toNat? | throw <| IO.userError "Invalid public test mode."
  require (mode < 8) "Invalid public test mode."
  let source ← unlockKeyFile path passwordFile mode.toUInt32
  require (source == path) "Unlock changed the original reservation path."
  checkSource source expected
  IO.println "PASS: protected encrypted/raw key identity and bound signature"

private def replacement (path passwordFile replacementPath : String) (raw : Bool) : IO Unit := do
  let source ← unlockKeyFile path passwordFile (if raw then 4 else 6)
  checkSource source "one"
  let prior ← readPrivate path
  let next ← readPrivate replacementPath
  replacePrivate path prior next
  if raw then
    checkSource source "two"
    IO.println "PASS: raw key files are reloaded before signing"
  else
    require (← failed <| publicKeyFromProtectedFile source)
      "An unlocked keystore ignored a changed protected source file."
    let digest := ByteArray.mk (Array.replicate 32 1)
    require (← failed <| signDigest65FromProtectedFile source digest)
      "An unlocked keystore signed after its protected source changed."
    IO.println "PASS: changed encrypted keystore blocks cached signing"

private def interactive (path expected : String) : IO UInt32 := do
  let result ← try
    try
      let source ← unlockKeyFile path "" 0
      require (source == path) "Interactive unlock changed the reservation path."
      checkSource source expected
      IO.println "KEYSTORE_READY_FOR_APPROVAL"
      require ((← (← IO.getStdin).getLine).trimAscii.toString == "APPROVE")
        "Pasted password typeahead reached a later approval."
      clearPromptKey
      require (← failed <| publicKeyFromProtectedFile source)
        "Clearing the native session left an encrypted keystore usable."
      IO.println "PASS: hidden keystore password, signing, paste isolation and cleanup"
      pure (0 : UInt32)
    finally clearPromptKey
  catch error =>
    IO.eprintln error.toString
    pure (1 : UInt32)
  IO.println s!"KEYSTORE_EXIT_CODE:{result}"
  -- Keep the controlling session alive for the PTY parent's termios check.
  let _ ← (← IO.getStdin).getLine
  return result

def main (args : List String) : IO UInt32 := do
  match args with
  | ["interactive", path, expected] => interactive path expected
  | _ =>
    try
      try
        match args with
        | ["probe", path, passwordFile, mode, expected] =>
            probe path passwordFile mode expected
        | ["replace", path, passwordFile, replacementPath] =>
            replacement path passwordFile replacementPath false
        | ["raw-reload", path, replacementPath] =>
            replacement path "" replacementPath true
        | ["cleanup", path, passwordFile] => do
            let _ ← unlockKeyFile path passwordFile 6
            checkSource path "one"
            clearPromptKey
            require (← failed <| publicKeyFromProtectedFile path)
              "Clearing the native session left the encrypted key usable."
            IO.println "PASS: encrypted native session cleanup"
        | _ => throw <| IO.userError "Invalid public keystore test invocation."
        return (0 : UInt32)
      finally clearPromptKey
    catch error =>
      IO.eprintln error.toString
      return (1 : UInt32)
