import Tornado.Spec.DepositBackupIntent
import LeanCrypto.HexWord

/-! Synthetic public byte inputs; no secrets, entropy sources or network. -/
open Tornado.Domain Tornado.Crypto Tornado.Cli

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error _ => throw <| IO.userError "Hex boundary regression check failed."

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def sameResult (left right : Except String ByteArray) : Bool :=
  match left, right with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def publicBytes (width : Nat) : ByteArray :=
  ByteArray.mk ((List.range width).toArray.map (fun index => (index * 73 + 19).toUInt8))

def main : IO UInt32 := do
  for width in [0, 1, 2, 31, 32, 62, 256, 4096] do
    let bytes := publicBytes width
    let raw := bytesToHex bytes
    require (raw == LeanCrypto.Hex.encode bytes && raw.length == 2 * width && raw.toLower == raw)
      "Actual byte serializer changed lowercase lexical or fixed-width output."
    require ((← checked <| parseHexBytes raw) == bytes &&
      (← checked <| parseHexBytes ("0x" ++ raw)) == bytes &&
      (← checked <| LeanCrypto.Hex.decode raw) == bytes &&
      (← checked <| LeanCrypto.Hex.decode ("0x" ++ raw)) == bytes)
      "Actual or structural parser failed an exact byte roundtrip."
  for byte in [0:256] do
    let bytes := ByteArray.mk #[byte.toUInt8]
    require (LeanCrypto.Hex.encode bytes == bytesToHex bytes &&
      (← checked <| parseHexBytes (bytesToHex bytes)) == bytes)
      "Exhaustive byte alphabet differs at a nibble boundary."
  for raw in ["", "0x", "00", "0x00", "aA", "0xAaBb", "0", "xx", "0xz", "0x0",
      "0X12", " 0x00", "é0", "aaz", "0xgg"] do
    require (sameResult (LeanCrypto.Hex.decode raw) (parseHexBytes raw))
      "Odd/nonhex/uppercase/prefix parser policy differs from the actual loop."
  let domain := 2 ^ 256
  for value in [0, 1, 15, 16, 255, 256, 257, 2 ^ 248, 2 ^ 255, domain - 1] do
    let text ← checked <| toHex32 value
    let bytes ← checked <| parseHexBytes text
    require (text.length == 66 && bytes.size == 32 && LeanCrypto.FixedBytes.decode bytes == value &&
      text == "0x" ++ bytesToHex (LeanCrypto.FixedBytes.encode 32 value))
      "Actual toHex32 serializer changed its canonical uint256 meaning."
  require (!(toHex32 domain).isOk && !(toHex32 (domain + 1)).isOk)
    "Out-of-range uint256 formatting was accepted."
  -- Exercise a proof-bearing source derived from the actual pure creator.
  let pool : Pool := allPools[7]!
  have supported : pool ∈ allPools := by
    change allPools[7]! ∈ allPools
    rw [getElem!_pos allPools 7 (by decide)]
    exact List.getElem_mem _
  let nullifierKey := ByteArray.mk (Array.replicate 32 0x11)
  let secretKey := ByteArray.mk (Array.replicate 32 0x22)
  let uuid := publicBytes 16
  match built : independentNoteFromEntropy pool nullifierKey secretKey uuid with
  | .error _ => throw <| IO.userError "Synthetic constructor failed."
  | .ok note =>
    let source := Tornado.Spec.DepositBackupIntent.Source.ofIndependent
      pool nullifierKey secretKey uuid note built supported
    let backup ← checked <| formatDepositBackup [note]
    let identities ← checked <| parseDepositBackup backup pool.chainId
    let items ← checked <| DepositMulti.publicItems backup pool.chainId
    require (identities.length == 1 && identities[0]!.publicIdentity.commitment == note.commitment &&
      identities[0]!.publicIdentity.nullifierHash == note.nullifierHash && items == source.items)
      "Actual constructor source did not connect to actual backup/funding parsing."
  let large := publicBytes (64 * 1024)
  require ((← checked <| LeanCrypto.Hex.decode (LeanCrypto.Hex.encode large)) == large)
    "Tail-recursive decoder failed the large public-byte stack boundary."
  IO.println "PASS: constructive byte/hex/toHex32 boundaries, exhaustive byte alphabet, parser negative controls, actual creator-to-backup certificate, and 64KiB stack boundary"
  return 0
