import Lean
import Tornado.SmartAccount.Recovery

open Lean Tornado.Domain Tornado.SmartAccount Tornado.Crypto

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def stringField (json : Json) (name : String) : Except String String :=
  (field json name).bind Json.getStr?

private def addressNat (text : String) : Except String Nat := do
  let bytes ← parseHexBytes text
  if bytes.size != 20 then throw "Invalid fixture address"
  return bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def decimalField (json : Json) (name : String) : Except String Nat := do
  let raw ← stringField json name
  let some value := raw.toNat? | throw "Invalid fixture decimal"
  return value

private def checkVectors (root : Json) : Except String Nat := do
  let vectors ← (← field root "vectors").getArr?
  let mut checked := 0
  for vector in vectors do
    let chainNumber ← (← field vector "chainId").getNat?
    let some chain := chainFromNat chainNumber | throw "Unknown fixture chain"
    let owner ← addressNat (← stringField vector "owner")
    let account ← addressNat (← stringField vector "account")
    let recipient ← addressNat (← stringField vector "recipient")
    let rawBalances ← (← field vector "balances").getArr?
    let mut balances := #[]
    for amount in rawBalances do
      let some value := (← amount.getStr?).toNat?
        | throw "Invalid fixture balance"
      balances := balances.push value
    let entryPointDeposit ← decimalField vector "entryPointDeposit"
    let planned ← planRecovery chain owner account recipient balances entryPointDeposit
    let expectedCalls ← (← field vector "calls").getArr?
    if planned.calls.size != expectedCalls.size then throw "Recovery call count differs"
    for (call, index) in planned.calls.toList.zipIdx do
      let expected := expectedCalls[index]!
      if call.to != (← addressNat (← stringField expected "to")) ||
          call.value != (← decimalField expected "value") ||
          "0x" ++ bytesToHex call.data != (← stringField expected "data") then
        throw "Recovery call differs from pinned viem vector"
    if "0x" ++ bytesToHex planned.data != (← stringField vector "data") ||
        (← toHex32 withdrawalAccountSalt) != (← stringField vector "factorySalt") ||
        "0x" ++ bytesToHex (← accountFactoryData owner) !=
          (← stringField vector "factoryData") then
      throw "Recovery batch or factory calldata differs from pinned viem vector"
    checked := checked + 1
  let owner := 1
  let account := 2
  let recipient := 3
  let balances := Array.replicate (assetsFor .mainnet).length 0
  if (planRecovery .mainnet owner account recipient balances 0).isOk then
    throw "Empty recovery accepted"
  if (planRecovery .mainnet 0 account recipient balances 1).isOk then
    throw "Zero owner accepted"
  if (planRecovery .mainnet owner account account balances 1).isOk then
    throw "Self-recipient accepted"
  if (planRecovery .mainnet owner account recipient #[0] 1).isOk then
    throw "Wrong balance count accepted"
  if (planRecovery .mainnet owner account recipient (balances.set! 0 (2 ^ 256)) 0).isOk then
    throw "Overflow balance accepted"
  if (accountFactoryData 0).isOk then throw "Zero owner factory call accepted"
  let delegate := (ByteArray.empty.push 0xef |>.push 0x01 |>.push 0x00) ++
    (ByteArray.mk (Array.replicate 20 0x11))
  if !ownerCodeAllowed ByteArray.empty || !ownerCodeAllowed delegate ||
      ownerCodeAllowed (delegate.push 0) || ownerCodeAllowed (ByteArray.empty.push 1) then
    throw "Owner-code delegation marker validation changed"
  if deployedAccountIdentityValid 1 2 3 1 2 4 ||
      !deployedAccountIdentityValid 1 2 3 1 2 3 then
    throw "Deployed account identity gate changed"
  return checked

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/recovery-vectors.json"
  match Json.parse raw >>= checkVectors with
  | .error error =>
    IO.eprintln error
    return 1
  | .ok checked =>
    if checked != 3 then
      IO.eprintln "Unexpected recovery vector count"
      return 1
    IO.println "PASS: 3 pinned smart-account recovery plans and 7 input/code guards"
    return 0
