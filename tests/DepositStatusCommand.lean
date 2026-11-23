import Tornado.Cli.DepositStatusCommand

namespace Tornado.Cli.DepositStatusCommand.Test

open Lean Tornado.Domain Tornado.Runtime
open Tornado.Cli.DepositStatusCommand

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def put (json : Json) (name : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert name value)
  | other => other

private def field (json : Json) (name : String) : IO Json :=
  unwrap (json.getObjVal? name)

private def str (json : Json) (name : String) : IO String := do
  unwrap (← field json name).getStr?

private def rejects (action : IO α) (message : String) : IO Unit := do
  let mut didReject := false
  try
    let _ ← action
  catch _ => didReject := true
  require didReject message

def main : IO UInt32 := do
  try
    let sequentialRaw ← IO.FS.readFile "fixtures/deposit-status-journal.json"
    let sequential ← unwrap (Json.parse sequentialRaw)
    let vectors ← unwrap (Json.parse (← IO.FS.readFile "fixtures/rpc-receipt-vectors.json"))
    let expected ← field vectors "expected"
    let responses ← field vectors "responses"
    let pool := "0x199112Eb461ea7eeC1D75B33343542e1d069B41c"
    let account := "0x52908400098527886E0F7030069857D2E4169EE7"
    let depositReceipt ← field (← field responses "depositChain") "result"
    let depositLogs ← unwrap (← field depositReceipt "logs").getArr?
    let depositLog := put depositLogs[0]! "address" (toJson pool)
    let depositReceipt := put (put (put depositReceipt "from" (toJson account))
      "to" (toJson pool)) "logs" (toJson #[depositLog])
    let depositHash ← str expected "depositTransactionHash"
    let chainFetch : JsonRpc.Method → Array Json → IO Json := fun method params =>
      match method with
      | .chainId => pure (toJson ("0x1" : String))
      | .getTransactionReceipt => do
          require (params == #[toJson depositHash]) "Sequential receipt queried another hash."
          pure depositReceipt
      | _ => throw <| IO.userError "Unexpected sequential RPC method."
    let noBundler : JsonRpc.Method → Array Json → IO Json := fun _ _ =>
      throw <| IO.userError "Sequential status used a bundler."
    let (updatedRaw, output) ← reconcileWith sequentialRaw chainFetch noBundler
    let updated ← unwrap (Json.parse updatedRaw)
    let steps ← unwrap (← field updated "steps").getArr?
    let originalSteps ← unwrap (← field sequential "steps").getArr?
    require ((← str steps[0]! "status") == "confirmed" && output.startsWith "1. confirmed")
      "Exact sequential Deposit event did not persist confirmed."
    require ((← str steps[0]! "commitment") == (← str originalSteps[0]! "commitment"))
      "Status update changed the protected note identity."
    let missing : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getTransactionReceipt then pure .null else chainFetch method params
    let (unknownRaw, _) ← reconcileWith sequentialRaw missing noBundler
    let unknownSteps ← unwrap (← field (← unwrap (Json.parse unknownRaw)) "steps").getArr?
    require ((← str unknownSteps[0]! "status") == "unknown")
      "Missing sequential receipt did not remain unknown."
    let wrongChain : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .chainId then pure (toJson ("0xaa" : String)) else chainFetch method params
    rejects (reconcileWith sequentialRaw wrongChain noBundler)
      "Wrong RPC chain could update a sequential journal."

    let entryPoint := Tornado.Cli.SmartAccountShow.entryPoint
    let sender ← str expected "sender"
    let userOpHash ← str expected "userOpHash"
    let nonce ← str expected "nonce"
    let batchHash ← str expected "batchDepositTransactionHash"
    let commitment ← str expected "commitment"
    let batchDeposit := Json.mkObj [
      ("pool", toJson pool), ("commitment", toJson commitment),
      ("denomination", toJson ("0.01" : String)),
      ("asset", toJson ("ETH" : String))]
    let batch := Json.mkObj [
      ("status", toJson ("submitted" : String)),
      ("deposits", toJson #[batchDeposit]),
      ("userOpHash", toJson userOpHash),
      ("transactionHash", toJson batchHash),
      ("nonce", toJson nonce)]
    let batchJournal := Json.mkObj [
      ("version", toJson (1 : Nat)),
      ("kind", toJson ("deposit-7702-batch" : String)),
      ("chainId", toJson (1 : Nat)),
      ("sender", toJson sender),
      ("entryPointAddress", toJson entryPoint),
      ("implementation", toJson ("0x1111111111111111111111111111111111111111" : String)),
      ("rpcUrl", toJson ("https://example.org/rpc" : String)),
      ("bundlerUrl", toJson ("https://example.org/bundler" : String)),
      ("createdAt", toJson ("2026-11-22T00:00:00.000Z" : String)),
      ("batches", toJson #[batch])]
    let batchReceipt ← field (← field responses "batchDepositChain") "result"
    let batchLogs ← unwrap (← field batchReceipt "logs").getArr?
    let batchLogs := #[(put batchLogs[0]! "address" (toJson entryPoint)),
      (put batchLogs[1]! "address" (toJson pool)),
      (put batchLogs[2]! "address" (toJson pool))]
    let batchReceipt := put (put batchReceipt "to" (toJson entryPoint))
      "logs" (toJson batchLogs)
    let batchFetch : JsonRpc.Method → Array Json → IO Json := fun method params =>
      match method with
      | .chainId => pure (toJson ("0x1" : String))
      | .getTransactionReceipt => do
          require (params == #[toJson batchHash]) "Batch receipt queried another hash."
          pure batchReceipt
      | _ => throw <| IO.userError "Unexpected batch RPC method."
    let (batchUpdatedRaw, batchOutput) ← reconcileWith batchJournal.compress batchFetch noBundler
    let batchUpdated ← unwrap (Json.parse batchUpdatedRaw)
    let batches ← unwrap (← field batchUpdated "batches").getArr?
    require ((← str batches[0]! "status") == "confirmed" &&
      batchOutput.startsWith "1/1 batch(es) confirmed")
      "Exact EntryPoint and Deposit events did not confirm batch."
    let noDepositReceipt := put batchReceipt "logs" (toJson #[batchLogs[0]!])
    let noDepositFetch : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getTransactionReceipt then pure noDepositReceipt
      else batchFetch method params
    let (incompleteRaw, _) ← reconcileWith batchJournal.compress noDepositFetch noBundler
    let incompleteBatches ← unwrap (← field (← unwrap (Json.parse incompleteRaw)) "batches").getArr?
    require ((← str incompleteBatches[0]! "status") == "unknown")
      "Batch without reviewed Deposit event was confirmed."
    let noHashBatch := put batch "transactionHash" .null
    let noHashJournal := put batchJournal "batches" (toJson #[noHashBatch])
    let bundler : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getUserOperationReceipt then do
        require (params == #[toJson userOpHash]) "Bundler queried another UserOperation."
        pure (Json.mkObj [("userOpHash", toJson userOpHash),
          ("receipt", Json.mkObj [("transactionHash", toJson batchHash)])])
      else throw <| IO.userError "Unexpected bundler method."
    let (hintedRaw, _) ← reconcileWith noHashJournal.compress batchFetch bundler
    let hintedBatches ← unwrap (← field (← unwrap (Json.parse hintedRaw)) "batches").getArr?
    require ((← str hintedBatches[0]! "status") == "confirmed" &&
      (← str hintedBatches[0]! "transactionHash") == batchHash)
      "Bundler hint was not checked against exact chain receipt."
    let fromBlockBatch := put noHashBatch "fromBlock" (toJson ("0x1" : String))
    let fromBlockJournal := put batchJournal "batches" (toJson #[fromBlockBatch])
    let logFetch : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getLogs then do
        require (params.size == 1) "EntryPoint log filter has wrong arity."
        let filter := params[0]!
        require ((← str filter "address") ==
          "0x4337084d9e255ff0702461cf8895ce9e3b5ff108")
          "EntryPoint log filter targets another contract."
        require ((← str filter "fromBlock") == "0x1")
          "EntryPoint log filter lost its lower block bound."
        pure (toJson #[batchLogs[0]!])
      else batchFetch method params
    let (foundRaw, _) ← reconcileWith fromBlockJournal.compress logFetch noBundler
    let foundBatches ← unwrap (← field (← unwrap (Json.parse foundRaw)) "batches").getArr?
    require ((← str foundBatches[0]! "status") == "confirmed" &&
      (← str foundBatches[0]! "transactionHash") == batchHash)
      "Filtered EntryPoint log did not locate an exact confirmed chain receipt."
    let ambiguousFetch : JsonRpc.Method → Array Json → IO Json := fun method params =>
      if method == .getLogs then pure (toJson #[batchLogs[0]!, batchLogs[0]!])
      else logFetch method params
    let (ambiguousRaw, _) ← reconcileWith fromBlockJournal.compress ambiguousFetch noBundler
    let ambiguousBatches ← unwrap (← field (← unwrap (Json.parse ambiguousRaw)) "batches").getArr?
    require ((← str ambiguousBatches[0]! "status") == "unknown")
      "Ambiguous EntryPoint logs were treated as one confirmed batch."
    IO.println "PASS: sequential and 7702 deposit status reconciliation"
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)

end Tornado.Cli.DepositStatusCommand.Test

def main : IO UInt32 := Tornado.Cli.DepositStatusCommand.Test.main
