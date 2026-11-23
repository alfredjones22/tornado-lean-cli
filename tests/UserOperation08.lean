import Lean
import Tornado.Protocol.UserOperation08

open Lean Tornado.Crypto Tornado.Protocol.UserOperation08

private def field (root : Json) (name : String) : Except String Json :=
  root.getObjVal? name

private def textField (root : Json) (name : String) : Except String String :=
  (field root name).bind Json.getStr?

private def optionalText (root : Json) (name : String) : Except String (Option String) :=
  match field root name with
  | .error _ => .ok none
  | .ok value => return some (← value.getStr?)

private def natField (root : Json) (name : String) : Except String Nat := do
  let raw ← textField root name
  let some value := raw.toNat? | throw s!"Invalid decimal fixture field {name}."
  return value

private def hexNibble (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

private def hexBytes (raw : String) : Except String ByteArray := do
  if !raw.startsWith "0x" || (raw.length - 2) % 2 != 0 then
    throw "Invalid hex fixture value."
  let chars := (raw.toList.drop 2).toArray
  let mut bytes := ByteArray.empty
  for i in [0:chars.size / 2] do
    let some hi := hexNibble chars[2 * i]! | throw "Invalid high hex nibble."
    let some lo := hexNibble chars[2 * i + 1]! | throw "Invalid low hex nibble."
    bytes := bytes.push (hi * 16 + lo).toUInt8
  return bytes

private def addressNat (raw : String) : Except String Nat := do
  let bytes ← hexBytes raw
  if bytes.size != 20 then throw "Fixture address must have 20 bytes."
  let mut value := 0
  for byte in bytes.data do value := value * 256 + byte.toNat
  return value

private def operationFromJson (root : Json) : Except String UserOperation := do
  let factory ← match (← optionalText root "factory") with
    | none => pure none
    | some "0x7702" => pure (some .eip7702Marker)
    | some address => pure (some (.address (← addressNat address)))
  let authorizationAddress ← match (← optionalText root "authorizationAddress") with
    | none => pure none
    | some address => pure (some (← addressNat address))
  let paymaster ← match (← optionalText root "paymaster") with
    | none => pure none
    | some address => pure (some (← addressNat address))
  let factoryData ← match (← optionalText root "factoryData") with
    | none => pure ByteArray.empty
    | some bytes => hexBytes bytes
  let paymasterData ← match (← optionalText root "paymasterData") with
    | none => pure ByteArray.empty
    | some bytes => hexBytes bytes
  let paymasterSignature ← match (← optionalText root "paymasterSignature") with
    | none => pure none
    | some bytes => pure (some (← hexBytes bytes))
  return {
    sender := (← addressNat (← textField root "sender")),
    nonce := (← natField root "nonce"),
    factory := factory,
    factoryData := factoryData,
    authorizationAddress := authorizationAddress,
    callData := (← hexBytes (← textField root "callData")),
    verificationGasLimit := (← natField root "verificationGasLimit"),
    callGasLimit := (← natField root "callGasLimit"),
    preVerificationGas := (← natField root "preVerificationGas"),
    maxPriorityFeePerGas := (← natField root "maxPriorityFeePerGas"),
    maxFeePerGas := (← natField root "maxFeePerGas"),
    paymaster := paymaster,
    paymasterVerificationGasLimit := (← match paymaster with
      | none => pure 0
      | some _ => natField root "paymasterVerificationGasLimit"),
    paymasterPostOpGasLimit := (← match paymaster with
      | none => pure 0
      | some _ => natField root "paymasterPostOpGasLimit"),
    paymasterData := paymasterData,
    paymasterSignature := paymasterSignature,
    signature := (← hexBytes (← textField root "signature"))
  }

private def checkedHex (actual : ByteArray) (expected : String) (label : String) : Except String Unit :=
  if "0x" ++ bytesToHex actual == expected then .ok ()
  else .error s!"UserOperation v0.8 mismatch: {label}."

private def checkVectors (root : Json) : Except String Nat := do
  let rows ← (← field root "cases").getArr?
  let signing ← field root "signing"
  let mut matched := 0
  let mut signed := false
  let mut paymasterHash : Option String := none
  for row in rows do
    let name ← textField row "name"
    let chainId ← (← field row "chainId").getNat?
    let entryPoint ← addressNat (← textField row "entryPointAddress")
    let operation ← operationFromJson (← field row "operation")
    let expected ← field row "expected"
    let packed ← pack operation
    checkedHex packed.initCode (← textField expected "initCode") (name ++ "/initCode")
    checkedHex packed.accountGasLimits (← textField expected "accountGasLimits") (name ++ "/accountGasLimits")
    checkedHex packed.gasFees (← textField expected "gasFees") (name ++ "/gasFees")
    checkedHex packed.paymasterAndData (← textField expected "paymasterAndData") (name ++ "/paymasterAndData")
    if let some expectedInit ← optionalText expected "transportInitCode" then
      checkedHex (← packTransport operation).initCode expectedInit (name ++ "/transportInitCode")
    if let some expectedTransport ← optionalText expected "transportPaymasterAndData" then
      checkedHex (← packTransport operation).paymasterAndData expectedTransport (name ++ "/transportPaymasterAndData")
    let digest ← userOperationHash chainId entryPoint operation
    checkedHex digest (← textField expected "hash") (name ++ "/hash")
    if name == "direct_paymaster" then paymasterHash := some ("0x" ++ bytesToHex digest)
    if name == "signature_changed" && paymasterHash != some ("0x" ++ bytesToHex digest) then
      throw "Changing the transport signature changed the v0.8 hash."
    if name == "separate_paymaster_signature" && paymasterHash == some ("0x" ++ bytesToHex digest) then
      throw "The separate paymaster signature marker was omitted from the v0.8 hash."
    if name == (← textField signing "case") then
      let privateKey ← hexBytes (← textField signing "privateKey")
      let signature ← signUserOperation privateKey chainId entryPoint operation
      checkedHex signature (← textField signing "signature") "deterministic typed-data signature"
      signed := true
    matched := matched + 1
  if !signed then throw "No signing fixture case was tested."
  return matched

private def checkRejections : Except String Unit := do
  let base : UserOperation := { sender := 0x1111111111111111111111111111111111111111 }
  if (uint128Bytes (2 ^ 128)).isOk then throw "Oversized uint128 was encoded."
  if (pack { base with verificationGasLimit := 2 ^ 128 }).isOk then
    throw "Oversized verification gas was packed."
  if (pack { base with maxFeePerGas := 2 ^ 128 }).isOk then
    throw "Oversized maximum gas fee was packed."
  if (pack { base with paymaster := some (2 ^ 160) }).isOk then
    throw "Oversized paymaster address was packed."
  if (userOperationHash 1 (2 ^ 160) base).isOk then
    throw "Oversized EntryPoint address was hashed."
  if (userOperationHash (2 ^ 256) 1 base).isOk then
    throw "Oversized chain ID was hashed."
  if (pack { base with nonce := 2 ^ 256 }).isOk then
    throw "Oversized nonce was packed."
  let oversized := { base with paymaster := some 1, paymasterSignature := some (ByteArray.mk (Array.replicate (2 ^ 16) 0)) }
  if (paymasterAndDataTransport oversized).isOk then
    throw "Oversized paymaster signature was transported."

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/userop08-vectors.json"
  let result : Except String Nat := do
    let root ← Json.parse raw
    let count ← checkVectors root
    checkRejections
    return count
  match result with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok count =>
      if count != 9 then
        IO.eprintln s!"Expected nine UserOperation vectors, found {count}."
        return 1
      IO.println "PASS: 9 viem v0.8 packed UserOperation/hash vectors, 1 signature, 8 rejection checks"
      return 0
