import Lean
import Tornado.Protocol.Rlp

open Lean Tornado.Crypto Tornado.Protocol.Rlp

private def repeated (count : Nat) (byte : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count byte)

private def field (root : Json) (name : String) : Except String String :=
  ((root.getObjVal? "cases").bind fun cases => cases.getObjVal? name).bind Json.getStr?

private def require (value : Bool) (message : String) : Except String Unit :=
  if value then .ok () else .error message

private def tx1 : Transaction1559 :=
  { chainId := 1, nonce := 0, maxPriorityFeePerGas := 1000000000,
    maxFeePerGas := 2000000000, gas := 21000,
    to := some 0x1111111111111111111111111111111111111111, value := 123 }

private def tx2 : Transaction1559 :=
  { chainId := 11155111, nonce := 7, maxPriorityFeePerGas := 2000000000,
    maxFeePerGas := 3000000000, gas := 100000, value := 0,
    data := ByteArray.mk #[0xab, 0xcd] }

private def tx3 : Transaction1559 :=
  { tx1 with nonce := 9, gas := 85000, to := some 0x2222222222222222222222222222222222222222, data := ByteArray.mk #[0x12, 0x34, 0x56], accessList := #[{ address := 0x1111111111111111111111111111111111111111, storageKeys := #[repeated 32 0x33] }] }

private def checkVectors (root : Json) : Except String Nat := do
  let sig : Signature := { yParity := 1, r := 1, s := 2 }
  let cases : List (String × Except String ByteArray) := [
    ("rlp_empty", .ok (bytes ByteArray.empty)),
    ("rlp_7f", .ok (bytes (ByteArray.mk #[0x7f]))),
    ("rlp_80", .ok (bytes (ByteArray.mk #[0x80]))),
    ("rlp_55", .ok (bytes (repeated 55 0x11))),
    ("rlp_56", .ok (bytes (repeated 56 0x11))),
    ("rlp_255", .ok (bytes (repeated 255 0x22))),
    ("rlp_256", .ok (bytes (repeated 256 0x22))),
    ("list_empty", .ok (list [])),
    ("list_mixed", .ok (list [bytes (ByteArray.mk #[0x01]), bytes ByteArray.empty,
      bytes (ByteArray.mk #[0x80])])),
    ("list_55", .ok (list [bytes (repeated 54 0xab)])),
    ("list_56", .ok (list [bytes (repeated 55 0xab)])),
    ("tx1_unsigned", serialize1559 tx1),
    ("tx2_unsigned", serialize1559 tx2),
    ("tx3_accesslist", serialize1559 tx3),
    ("tx1_signed", serialize1559 tx1 (some sig)),
    ("tx1_signing_hash", signingHash1559 tx1),
    ("tx1_transaction_hash", transactionHash1559 tx1 sig),
    ("auth_chain1", authorizationHash7702 1
      0x2222222222222222222222222222222222222222 0),
    ("auth_wildcard", authorizationHash7702 0
      0x1111111111111111111111111111111111111111 1),
    ("auth_sepolia", authorizationHash7702 11155111
      0x1111111111111111111111111111111111111111 255)
  ]
  let mut count := 0
  for (name, actual) in cases do
    let expected ← field root name
    let bytes ← actual
    if "0x" ++ bytesToHex bytes != expected then
      throw s!"RLP/transaction vector mismatch: {name}"
    count := count + 1
  return count

private def checkRejections : Except String Unit := do
  require ((serialize1559 { tx1 with chainId := 0 }).isOk == false)
    "Zero chain ID accepted."
  require ((serialize1559 { tx1 with chainId := 2 ^ 256 }).isOk == false)
    "Oversized chain ID accepted."
  require ((serialize1559 { tx1 with nonce := 2 ^ 256 }).isOk == false)
    "Oversized nonce accepted."
  require ((serialize1559 { tx1 with maxPriorityFeePerGas := 2000000001 }).isOk == false)
    "Priority fee above max fee accepted."
  require ((serialize1559 { tx1 with to := some (2 ^ 160) }).isOk == false)
    "Oversized recipient accepted."
  require ((serialize1559 { tx3 with accessList := #[{ address := 0x1111111111111111111111111111111111111111, storageKeys := #[repeated 31 0x33] }] }).isOk == false)
    "Short access-list key accepted."
  require ((serialize1559 tx1 (some { yParity := 2, r := 1, s := 2 })).isOk == false)
    "Invalid signature parity accepted."
  require ((serialize1559 tx1 (some { yParity := 0, r := 0, s := 2 })).isOk == false)
    "Zero signature scalar accepted."
  require ((authorizationHash7702 1 (2 ^ 160) 0).isOk == false)
    "Oversized authorization address accepted."
  require ((authorizationHash7702 (2 ^ 256) 1 0).isOk == false)
    "Oversized authorization chain accepted."

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/rlp-vectors.json"
  let checked : Except String Nat := do
    let json ← Json.parse raw
    let count ← checkVectors json
    checkRejections
    return count
  match checked with
  | .error message =>
      IO.eprintln message
      return 1
  | .ok count =>
      IO.println s!"PASS: {count} pinned viem RLP/EIP-1559/EIP-7702 vectors and 10 rejections"
      return 0
