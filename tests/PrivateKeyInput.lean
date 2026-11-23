import Tornado.Cli.PrivateKeyInput

namespace Tornado.Cli.PrivateKeyInput.Test

private def require (value : Bool) (message : String) : IO Unit :=
  unless value do throw <| IO.userError message

private def equalsKey (value : Except String ByteArray) (expected : ByteArray) : Bool :=
  match value with
  | .ok bytes => bytes == expected
  | .error _ => false

private def rejected (value : Except String ByteArray) : Bool :=
  match value with
  | .error _ => true
  | .ok _ => false

private def redactedError (value : Except String ByteArray) : Bool :=
  match value with
  | .error message => message == "Key file must contain only a 32-byte hex private key."
  | .ok _ => false

def main : IO UInt32 := do
  let key := ("0x" ++ String.ofList (List.replicate 63 '0') ++ "1").toUTF8
  let expected := ByteArray.mk (Array.replicate 31 0 ++ #[1])
  let surrounded := ByteArray.mk #[0xef, 0xbb, 0xbf, 0x09] ++ key ++
    ByteArray.mk #[0xc2, 0xa0, 0xe3, 0x80, 0x80]
  require (equalsKey (PrivateKeyInput.parse key) expected)
    "A canonical protected key was not decoded."
  require (equalsKey (PrivateKeyInput.parse surrounded) expected)
    "Surrounding JavaScript whitespace changed the protected key."
  require (rejected (PrivateKeyInput.parse (key ++ ByteArray.mk #[0])))
    "A trailing NUL was accepted."
  require (rejected (PrivateKeyInput.parse ("0X" ++ String.ofList (List.replicate 64 'a')).toUTF8))
    "An uppercase prefix was accepted."
  require (rejected (PrivateKeyInput.parse ("0x" ++ String.ofList (List.replicate 63 '0') ++ "g").toUTF8))
    "A non-hex key byte was accepted."
  require (redactedError (PrivateKeyInput.parse ("0x" ++ String.ofList (List.replicate 63 '0') ++ "g").toUTF8))
    "A malformed private key was echoed into an error."
  require (rejected (PrivateKeyInput.parse (ByteArray.mk (Array.replicate 1025 0x20))))
    "Oversized key input was accepted."
  IO.println "PASS: byte-only private-key parsing, trim parity, and malformed-input rejection"
  return 0

end Tornado.Cli.PrivateKeyInput.Test

def main : IO UInt32 := Tornado.Cli.PrivateKeyInput.Test.main
