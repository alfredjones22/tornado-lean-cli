import Tornado.Cli.SmartAccountShow

open Lean Tornado.Domain Tornado.Crypto Tornado.Runtime Tornado.SmartAccount
open Tornado.Cli.SmartAccountShow

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check : Except String Unit := do
  let ownerText := "0x52908400098527886E0F7030069857D2E4169EE7"
  let owner ← parseOwner ownerText
  require ((← checksumAddress owner) == ownerText) "EIP-55 checksum changed."
  require ((← parseOwner ownerText.toLower) == owner) "Lowercase address was rejected."
  require (!(parseOwner "0x52908400098527886E0F7030069857D2E4169Ee7").isOk)
    "Invalid mixed-case EIP-55 address was accepted."
  require (!(parseOwner "0x0000000000000000000000000000000000000000").isOk)
    "Zero owner was accepted."
  require (!(parseOwner "0x1234").isOk) "Short owner was accepted."

  let getAddressCall ← getAddressData owner
  let expectedCall :=
    "0x8cb84e1800000000000000000000000052908400098527886e0f7030069857d2e4169ee7" ++
    "ad20024a41a36c5c1a4f99e4b85029a2ed850d222ec2f53842b9f5e67b2cae1d"
  require ("0x" ++ bytesToHex getAddressCall == expectedCall)
    "Factory getAddress calldata differs from viem."
  require (!(getAddressData 0).isOk) "Zero owner factory call was accepted."

  let request := callParams simpleAccountFactory getAddressCall "0x1234"
  require (request.size == 2) "eth_call request arity changed."
  let call := request[0]!
  require ((← (← call.getObjVal? "to").getStr?) == simpleAccountFactory)
    "eth_call target changed."
  require ((← (← call.getObjVal? "data").getStr?) == expectedCall)
    "eth_call data changed."
  require ((← request[1]!.getStr?) == "0x1234") "Block binding changed."
  require ((slotParams ownerText "0x1234").size == 3)
    "Storage request arity changed."

  let response ← Json.parse
    "{\"jsonrpc\":\"2.0\",\"id\":7,\"result\":\"0x00000000000000000000000052908400098527886e0f7030069857d2e4169ee7\"}"
  let addressValue ← JsonRpc.decodeResult 7 response
  require ((← decodeAddressResult addressValue) == owner)
    "Public RPC-shaped address word was rejected."
  require (!(JsonRpc.decodeResult 8 response).isOk)
    "Mismatched JSON-RPC ID was accepted."
  require (!(decodeAddressResult (toJson
    "0x10000000000000000000000052908400098527886e0f7030069857d2e4169ee7")).isOk)
    "ABI address with nonzero high bytes was accepted."
  require (!(decodeAddressResult (toJson "0x1234")).isOk)
    "Short ABI address was accepted."
  require ((← decodeUintResult (toJson
    "0x000000000000000000000000000000000000000000000000000000000000002a")) == 42)
    "ABI uint256 result changed."
  require (!(decodeUintResult (toJson "0x2a")).isOk)
    "Short ABI uint256 was accepted."
  require ((← decodeQuantityResult (toJson "0x2a")) == 42)
    "Canonical RPC quantity was rejected."
  require (!(decodeQuantityResult (toJson "0x02a")).isOk)
    "Noncanonical RPC quantity was accepted."
  require ((← decodeCodeResult (toJson "0x")).isEmpty)
    "Empty owner code was rejected."
  require (!(decodeCodeResult (toJson "0x123")).isOk)
    "Odd-length code was accepted."
  require ((← decodeSlotResult (toJson
    "0x00000000000000000000000052908400098527886e0f7030069857d2e4169ee7")) == owner)
    "Implementation slot decoding changed."
  require (!(decodeSlotResult (toJson "0x0")).isOk)
    "Short implementation slot was accepted."

  let account : Account := ⟨owner, owner, false, 12⟩
  let assets := assetsFor .mainnet
  let amounts := [1000000000000000000, 100000000000000000000,
    1250000, 1234567, 12345678]
  let rows : Array BalanceRow :=
    ((assets.zip amounts).map fun (asset, amount) => ⟨asset, amount⟩).toArray
  let rendered ← render .mainnet account rows 500000000000000000
  let expected :=
    "Owner: 0x52908400098527886E0F7030069857D2E4169EE7\n" ++
    "Smart account: 0x52908400098527886E0F7030069857D2E4169EE7\n" ++
    "Deployed: no\n" ++
    "EntryPoint nonce: 12\n" ++
    "ETH: 1\nDAI: 100\nUSDC: 1.25\nUSDT: 1.234567\nWBTC: 0.12345678\n" ++
    "EntryPoint deposit: 0.5 ETH\n"
  require (rendered == expected) "Smart-account show output changed."
  require (!(render .sepolia account rows 0).isOk)
    "Balances from the wrong chain were accepted."
  require (!(render .mainnet account (rows.set! 0
    { asset := assets.head!, amount := 2 ^ 256 }) 0).isOk)
    "Overflow balance was accepted."
  return ()

private def checkOptions : IO Unit := do
  let help ← showCommand ["--help"]
  unless help.startsWith "Usage: tornado smart-account show" do
    throw <| IO.userError "Show help changed."
  let mut rejected := false
  try
    let _ ← showCommand ["--owner", "0x1234"]
  catch _ =>
    rejected := true
  unless rejected do throw <| IO.userError "Invalid owner reached the network."

def main : IO UInt32 := do
  match check with
  | .error message =>
      IO.eprintln message
      return 1
  | .ok _ =>
      try
        checkOptions
        IO.println "PASS: offline smart-account show request, response, and output checks"
        return 0
      catch error =>
        IO.eprintln error.toString
        return 1
