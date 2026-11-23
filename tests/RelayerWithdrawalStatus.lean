import Tornado.Cli.RelayerWithdrawalStatus

namespace Tornado.Cli.RelayerWithdrawalStatus.Test

open Lean Tornado.Domain Tornado.Runtime
open Tornado.Cli.RelayerWithdrawalStatus

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def field (json : Json) (name : String) : IO Json :=
  unwrap (json.getObjVal? name)

private def string (json : Json) (name : String) : IO String := do
  unwrap (← field json name).getStr?

private def put (json : Json) (name : String) (value : Json) : Json :=
  match json with
  | .obj entries => .obj (entries.insert name value)
  | other => other

private def requireStatus (record : Json)
    (fetch : JsonRpc.Method → Array Json → IO Json)
    (expected : String) (exitCode : UInt32) : IO Json := do
  let (updatedRaw, output, code) ← reconcileWith record.compress fetch
  let updated ← unwrap (Json.parse updatedRaw)
  require ((← string updated "status") == expected && code == exitCode &&
    output.startsWith ("Status: " ++ expected))
    s!"Relayer reconciliation yielded the wrong {expected} result."
  return updated

def main : IO UInt32 := do
  try
    let vectors ← unwrap (Json.parse (← IO.FS.readFile "fixtures/rpc-receipt-vectors.json"))
    let expected ← field vectors "expected"
    let responses ← field vectors "responses"
    let pool := "0x12D66f87A04A9E220743712cE6d9bB1B5616B8Fc"
    let txHash ← string expected "relayerTransactionHash"
    let nullifier ← string expected "nullifierHash"
    let recipient ← string expected "recipient"
    let reward ← string expected "relayer"
    let fee ← string expected "fee"
    let receipt ← field (← field responses "relayerChain") "result"
    let logs ← unwrap (← field receipt "logs").getArr?
    let log := put logs[0]! "address" (toJson pool)
    let receipt := put (put receipt "to" (toJson pool)) "logs" (toJson #[log])
    let record := Json.mkObj [
      ("version", toJson (1 : Nat)), ("kind", toJson ("relayer" : String)),
      ("chainId", toJson (1 : Nat)), ("poolAddress", toJson pool),
      ("nullifierHash", toJson nullifier), ("recipient", toJson recipient),
      ("relayerUrl", toJson ("https://relayer.example/" : String)),
      ("rewardAccount", toJson reward), ("fee", toJson fee),
      ("fromBlock", toJson ("0x1234" : String)),
      ("rpcUrl", toJson ("https://ethereum.publicnode.com" : String)),
      ("status", toJson ("unknown" : String))]
    require ((parseRecord record).isOk) "Pinned Classic pool record was rejected."
    let fetch : JsonRpc.Method → Array Json → IO Json := fun method params =>
      match method with
      | .chainId => pure (toJson ("0x1" : String))
      | .blockNumber => pure (toJson ("0x1234" : String))
      | .getLogs => do
          require (params.size == 1) "Pool log scan has wrong request arity."
          let filter := params[0]!
          require ((← string filter "address") == pool.toLower &&
            (← string filter "fromBlock") == "0x1234" &&
            (← string filter "toBlock") == "0x1234")
            "Pool log scan changed target or block bounds."
          let topics ← unwrap (← field filter "topics").getArr?
          require (topics.size == 1 && topics[0]! ==
            toJson ("0x" ++ Tornado.Crypto.bytesToHex Tornado.Protocol.Events.withdrawalTopic))
            "Pool scan leaked the nullifier or used another event topic."
          pure (toJson #[log])
      | .getTransactionReceipt => do
          require (params == #[toJson txHash]) "Wrong relayer transaction was queried."
          pure receipt
      | _ => throw <| IO.userError "Unexpected relayer status RPC method."
    let confirmed ← requireStatus record fetch "confirmed" 0
    require ((← string confirmed "transactionHash") == txHash)
      "Confirmed relayer status omitted the exact transaction hash."
    let wrongRecipient := put record "recipient"
      (toJson ("0x9999999999999999999999999999999999999999" : String))
    let wrong ← requireStatus wrongRecipient fetch "unknown" 2
    require ((← string wrong "transactionHash") == txHash)
      "Wrong-recipient withdrawal did not retain its chain transaction hint."
    let ambiguous : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getLogs then pure (toJson #[log, log]) else fetch method params
    let _ ← requireStatus record ambiguous "unknown" 2
    let noReceipt : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getTransactionReceipt then pure .null else fetch method params
    let _ ← requireStatus record noReceipt "unknown" 2
    let revertedReceipt := put receipt "status" (toJson ("0x0" : String))
    let reverted : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getTransactionReceipt then pure revertedReceipt else fetch method params
    let _ ← requireStatus record reverted "unknown" 2
    -- TypeScript omits optional fields rather than serializing null.
    let direct := Json.mkObj [
      ("version", toJson (1 : Nat)), ("kind", toJson ("relayer" : String)),
      ("chainId", toJson (1 : Nat)), ("poolAddress", toJson pool),
      ("nullifierHash", toJson nullifier), ("recipient", toJson recipient),
      ("relayerUrl", toJson ("https://relayer.example/" : String)),
      ("rewardAccount", toJson reward), ("fee", toJson fee),
      ("transactionHash", toJson txHash),
      ("rpcUrl", toJson ("https://ethereum.publicnode.com" : String)),
      ("status", toJson ("unknown" : String))]
    let directFetch : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getLogs then
        throw <| IO.userError "Direct hash status should not scan pool history."
      else fetch method params
    let _ ← requireStatus direct directFetch "confirmed" 0
    let noHash := Json.mkObj [
      ("version", toJson (1 : Nat)), ("kind", toJson ("relayer" : String)),
      ("chainId", toJson (1 : Nat)), ("poolAddress", toJson pool),
      ("nullifierHash", toJson nullifier), ("recipient", toJson recipient),
      ("relayerUrl", toJson ("https://relayer.example/" : String)),
      ("rewardAccount", toJson reward), ("fee", toJson fee),
      ("rpcUrl", toJson ("https://ethereum.publicnode.com" : String)),
      ("status", toJson ("unknown" : String))]
    let _ ← requireStatus noHash directFetch "unknown" 2
    let wrongChain : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .chainId then pure (toJson ("0xaa" : String)) else fetch method params
    let _ ← requireStatus record wrongChain "unknown" 2
    require (!(parseRecord (put record "poolAddress" (toJson
      ("0x199112Eb461ea7eeC1D75B33343542e1d069B41c" : String)))).isOk)
      "Non-Classic pool was accepted for relayer status."
    IO.println "PASS: exact Classic relayer chain event, receipt, ambiguity, and no-job safety"
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)

end Tornado.Cli.RelayerWithdrawalStatus.Test

def main : IO UInt32 := Tornado.Cli.RelayerWithdrawalStatus.Test.main
