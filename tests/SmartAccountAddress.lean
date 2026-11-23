import Tornado.Cli.SmartAccountShow
import Tornado.SmartAccount.Address

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.SmartAccount
open Tornado.Cli.SmartAccountShow

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def field (json : Json) (key : String) : IO Json :=
  checked <| json.getObjVal? key

private def text (json : Json) (key : String) : IO String := do
  checked <| (← field json key).getStr?

private def hexNat (raw : String) : IO Nat := do
  let bytes ← checked <| parseHexBytes raw
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

def main : IO UInt32 := do
  let fixture ← checked <| Json.parse
    (← IO.FS.readFile "fixtures/smart-account-address-vectors.json")
  let template ← checked <| parseHexBytes (← text fixture "factoryRuntimeTemplate")
  let mut reconstructed := template
  let slots ← checked <| (← field fixture "immutables").getArr?
  require (slots.size == 5) "Pinned factory immutable reference count changed"
  for slot in slots do
    let offset ← checked <| (← field slot "offset").getNat?
    let value ← hexNat (← text slot "value")
    let bytes ← checked <| Abi.addressWord value
    require (offset + bytes.size <= reconstructed.size)
      "Factory immutable lies outside the pinned runtime"
    for i in [0:bytes.size] do
      reconstructed := reconstructed.set! (offset + i) bytes[i]!
  require (pinnedFactoryCode reconstructed &&
    "0x" ++ bytesToHex (keccak256 reconstructed) == (← text fixture "factoryRuntimeHash"))
    "Offline factory reconstruction differs from the preexisting runtime pin"
  let proxy ← checked Address.proxyCreationCode
  let offset ← checked <| (← field fixture "proxyCreationOffset").getNat?
  let count ← checked <| (← field fixture "proxyCreationBytes").getNat?
  require (proxy.size == 680 && count == 680 &&
    reconstructed.extract offset (offset + count) == proxy &&
    "0x" ++ bytesToHex proxy == (← text fixture "proxyCreationCode"))
    "Proxy creation bytes are not the exact pinned factory's embedded code"
  require (Address.factory == (← hexNat (← text fixture "factory")) &&
    Address.implementation == (← hexNat (← text fixture "implementation")) &&
    Address.withdrawalSalt == (← hexNat (← text fixture "salt")) &&
    Address.withdrawalSalt == withdrawalAccountSalt)
    "Pinned prediction identity differs from the CLI factory or salt"
  let implementationCode ← checked <| parseHexBytes
    (← text fixture "implementationRuntimeCode")
  require (pinnedImplementationCode implementationCode && implementationCode.size == 6362)
    "Offline implementation runtime differs from its preexisting v0.8 pin"
  let cases ← checked <| (← field fixture "cases").getArr?
  require (cases.size == 6) "Local account prediction vectors are missing"
  for row in cases do
    let owner ← hexNat (← text row "owner")
    let salt ← hexNat (← text row "salt")
    let expected ← hexNat (← text row "account")
    let actual ← checked <| Address.predictWithSalt owner salt
    require (actual == expected) "Native CREATE2 prediction differs from pinned viem"
    require ("0x" ++ bytesToHex (← checked <| Address.initCodeHash owner) ==
      (← text row "initCodeHash")) "Proxy constructor encoding differs from viem"
    if salt == Address.withdrawalSalt then
      require ((← checked <| Address.predict owner) == expected)
        "Default withdrawal salt prediction changed"
      let _ ← checked <| Address.validateReported owner Address.implementation actual
      require (!(Address.validateReported owner Address.implementation (actual + 1)).isOk)
        "A provider-substituted smart-account destination was accepted"
      require (!(Address.validateReported owner (Address.implementation + 1) actual).isOk)
        "A provider-substituted implementation address was accepted"
      let identity : IdentityReadings := {
        owner, factoryCode := reconstructed, ownerCode := ByteArray.empty,
        implementation := Address.implementation, implementationCode,
        implementationEntryPoint := 0x4337084d9e255ff0702461cf8895ce9e3b5ff108,
        account := actual, accountCode := ByteArray.empty, nonce := 0 }
      let accepted ← checked <| validateIdentity identity
      require (accepted.owner == owner && accepted.address == actual && !accepted.deployed)
        "A valid locally predicted identity was rejected"
      let forged := { identity with
        account := actual + 1
        accountCode := ByteArray.mk #[0x60, 0x01]
        actualOwner := some owner
        actualEntryPoint := some identity.implementationEntryPoint
        slotValue := some Address.implementation }
      match validateIdentity forged with
      | .ok _ => throw <| IO.userError "RPC identity validation accepted a substituted destination"
      | .error message => do
        require (message ==
            "Smart-account address differs from the local pinned-factory prediction.")
          "The independent destination check did not precede later RPC claims"
  require (!(Address.predict 0).isOk && !(Address.predict (2 ^ 160)).isOk &&
    !(Address.predictWithSalt 1 (2 ^ 256)).isOk)
    "Out-of-domain CREATE2 input was accepted"
  IO.println "PASS: six native CREATE2 vectors, pinned factory reconstruction, and forged RPC destination rejection"
  return 0
