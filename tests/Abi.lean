import Lean
import Tornado.Protocol.Abi

open Lean Tornado.Protocol.Abi Tornado.Crypto

private def fieldString (root : Json) (name : String) : Except String String :=
  (root.getObjVal? "cases").bind (fun cases => (cases.getObjVal? name).bind Json.getStr?)

private def byteRepeat (count : Nat) (value : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count value)

private def checkVectors (root : Json) : Except String Nat := do
  let a : Nat := 0x1111111111111111111111111111111111111111
  let b : Nat := 0x2222222222222222222222222222222222222222
  let ab := byteRepeat 32 0xab
  let rootWord := byteRepeat 32 0x11
  let nullifierHash := byteRepeat 32 0x22
  let short := ByteArray.mk #[0x12, 0x34]
  let empty := ByteArray.empty
  let callOne : ContractCall := { to := a, value := 1, data := short }
  let callTwo : ContractCall := { to := b, value := 0, data := empty }
  let pair := #[callOne, callTwo]
  let sponsorShort : SponsorData := ⟨a, short, rootWord, nullifierHash, b, 17⟩
  let sponsorEmpty : SponsorData := { sponsorShort with proof := empty, fee := 0 }
  let vectors : List (String × Except String ByteArray) := [
    ("approve_5", erc20Approve a 5),
    ("transfer_high", erc20Transfer b (2 ^ 255)),
    ("deposit", poolDeposit ab),
    ("pool_withdraw_short", poolWithdraw short rootWord nullifierHash a b 17 0),
    ("pool_withdraw_empty", poolWithdraw empty rootWord nullifierHash a b 17 0),
    ("execute_short", accountExecute a 1 short),
    ("execute_empty", accountExecute b 0 empty),
    ("execute_batch_empty", accountExecuteBatch #[]),
    ("execute_batch_one", accountExecuteBatch #[callOne]),
    ("execute_batch_two", accountExecuteBatch pair),
    ("call_params_two", callArrayParameters pair),
    ("calls_hash_two", callsHash pair),
    ("withdraw_deposit", accountWithdrawDepositTo a 123),
    ("sponsor_short", sponsorParameters sponsorShort),
    ("sponsor_empty", sponsorParameters sponsorEmpty)
  ]
  let mut matched := 0
  for (name, result) in vectors do
    let expected ← fieldString root name
    let actual ← result
    if "0x" ++ bytesToHex actual != expected then
      throw s!"ABI vector mismatch: {name}"
    matched := matched + 1
  if (← decodeSponsorParameters (← sponsorParameters sponsorShort)) != sponsorShort then
    throw "Sponsor short tuple roundtrip failed."
  if (← decodeSponsorParameters (← sponsorParameters sponsorEmpty)) != sponsorEmpty then
    throw "Sponsor empty tuple roundtrip failed."
  return matched

private def checkRejections : Except String Nat := do
  let a : Nat := 0x1111111111111111111111111111111111111111
  let good : ContractCall := { to := a, value := 0, data := ByteArray.empty }
  let zero : ContractCall := { good with to := 0 }
  let bigAddress : ContractCall := { good with to := 2 ^ 160 }
  let bigValue : ContractCall := { good with value := 2 ^ 256 }
  let hugeData : ContractCall := { good with data := byteRepeat 16385 0 }
  let totalData : ContractCall := { good with data := byteRepeat 14000 0 }
  let invalid : List Bool := [
    (uintWord (2 ^ 256)).isOk, (addressWord (2 ^ 160)).isOk,
    (bytes32Word (byteRepeat 31 0)).isOk,
    (erc20Transfer a (2 ^ 256)).isOk,
    (poolWithdraw ByteArray.empty (byteRepeat 31 0) (byteRepeat 32 0) a a 0 0).isOk,
    (validateCalls #[zero]).isOk, (validateCalls #[bigAddress]).isOk,
    (validateCalls #[bigValue]).isOk, (validateCalls #[good] (some a)).isOk,
    (validateCalls #[hugeData]).isOk,
    (validateCalls (Array.replicate 13 good)).isOk,
    (validateCalls (Array.replicate 5 totalData)).isOk
  ]
  if invalid.any id then throw "Unsafe ABI shape was accepted."
  let sponsor : SponsorData := ⟨a, ByteArray.mk #[0x12, 0x34],
    byteRepeat 32 0x11, byteRepeat 32 0x22, a, 1⟩
  let encoded ← sponsorParameters sponsor
  if (decodeSponsorParameters (encoded.extract 0 (encoded.size - 1))).isOk then
    throw "Truncated sponsor tuple was accepted."
  let badOffset := (ByteArray.mk #[1]) ++ (encoded.extract 1 encoded.size)
  if (decodeSponsorParameters badOffset).isOk then
    throw "Bad sponsor offset was accepted."
  let badPadding := encoded.extract 0 (encoded.size - 1) ++ (ByteArray.mk #[1])
  if (decodeSponsorParameters badPadding).isOk then
    throw "Nonzero sponsor padding was accepted."
  return invalid.length + 3

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/abi-vectors.json"
  let result := do
    let root ← Json.parse raw
    let vectors ← checkVectors root
    let rejected ← checkRejections
    return (vectors, rejected)
  match result with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok (vectors, rejected) =>
      IO.println s!"PASS: {vectors} viem ABI vectors, 2 sponsor roundtrips, {rejected} rejection checks"
      return 0
