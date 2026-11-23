import Tornado.Cli.WithdrawalStatusCommand

namespace Tornado.Cli.WithdrawalStatusCommand.Test

open Lean Tornado.Domain Tornado.Cli.WithdrawalStatusCommand
open Tornado.Runtime

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def field (json : Json) (name : String) : IO Json :=
  unwrap (json.getObjVal? name)

private def string (json : Json) (name : String) : IO String := do
  unwrap ((← field json name).getStr?)

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def statusFrom (expected : Json) : IO OneNoteStatus := do
  let userOpHash ← string expected "userOpHash"
  let entryPointAddress ← string expected "entryPoint"
  let sender ← string expected "sender"
  let paymaster ← string expected "paymaster"
  let nonce ← string expected "nonce"
  let poolAddress ← string expected "pool"
  let recipient ← string expected "recipient"
  let fee ← string expected "fee"
  let nullifierHash ← string expected "nullifierHash"
  let result : OneNoteStatus := {
    chainId := ChainId.mainnet,
    userOpHash := userOpHash, entryPointAddress := entryPointAddress,
    sender := sender, paymaster := paymaster, nonce := nonce,
    poolAddress := poolAddress, recipient := recipient, fee := fee,
    nullifierHash := nullifierHash,
    fromBlock := some "0x1200", status := WithdrawalState.unknown }
  return result

def main : IO UInt32 := do
  try
    let root ← unwrap (Json.parse (← IO.FS.readFile "fixtures/rpc-receipt-vectors.json"))
    let expected ← field root "expected"
    let responses ← field root "responses"
    let status ← statusFrom expected
    let chainBase ← field (← field responses "chain") "result"
    let logs ← unwrap ((← field chainBase "logs").getArr?)
    let poolLog := logs[1]!
    let topics ← unwrap ((← field poolLog "topics").getArr?)
    let paymaster ← string expected "paymaster"
    let paddedPaymaster := "0x" ++ String.ofList (List.replicate 24 '0') ++
      String.ofList (paymaster.toList.drop 2)
    let changedPoolLog := poolLog.setObjVal! "topics"
      (Json.arr (topics.set! 1 (toJson paddedPaymaster)))
    let chain := chainBase.setObjVal! "logs"
      (Json.arr (logs.set! 1 changedPoolLog))
    let bundler ← field (← field responses "bundler") "result"
    let failedChain ← field (← field responses "failedChain") "result"
    let failedBundler ← field (← field responses "failedBundler") "result"
    let txHash ← string expected "transactionHash"
    let failedTxHash ← string expected "failedTransactionHash"
    let success : String → JsonRpc.Method → Array Json → IO Json :=
      fun url method params => do
        if method == .chainId then return toJson ("0x1" : String)
        if url == "bundler" && method == .getUserOperationReceipt then return bundler
        if url == "rpc" && method == .getTransactionReceipt then
          require (params == #[toJson txHash]) "Receipt query changed transaction hash."
          return chain
        throw <| IO.userError "Unexpected success RPC request."
    let exact ← inspectWith status "rpc" "bundler" success
    require (exact.status == .confirmed)
      s!"Exact one-note chain and bundler evidence was not confirmed: {repr exact.status}, {exact.message}."
    let otherHash := "0x" ++ String.ofList (List.replicate 64 'd')
    let competing := { status with userOpHash := otherHash }
    let candidateRecord : WithdrawalStatusRecord :=
      { current := competing, candidates := some [competing, status] }
    let (_, aggregate, candidates) ← inspectRecordWith candidateRecord "rpc" "bundler" success
    require (aggregate.status == .confirmed && candidates.length == 2 &&
      candidates.head!.2.status == .unknown)
      "One exact included candidate did not win over another unknown candidate."
    let original := Json.mkObj [
      ("userOpHash", toJson otherHash), ("fee", toJson status.fee),
      ("status", toJson ("unknown" : String)),
      ("preserve", toJson ("public marker" : String)),
      ("candidates", Json.arr #[
        Json.mkObj [("userOpHash", toJson otherHash), ("fee", toJson status.fee),
          ("status", toJson ("unknown" : String))],
        Json.mkObj [("userOpHash", toJson status.userOpHash), ("fee", toJson status.fee),
          ("status", toJson ("unknown" : String))]])]
    let updated ← unwrap (updatedJournalJson original candidateRecord status aggregate candidates)
    require ((← string updated "userOpHash") == status.userOpHash &&
      (← string updated "status") == "confirmed" &&
      (← string updated "preserve") == "public marker")
      "Candidate reconciliation did not persist the confirmed aggregate safely."
    let failed : String → JsonRpc.Method → Array Json → IO Json :=
      fun url method params => do
        if method == .chainId then return toJson ("0x1" : String)
        if url == "bundler" && method == .getUserOperationReceipt then return failedBundler
        if url == "rpc" && method == .getTransactionReceipt then
          require (params == #[toJson failedTxHash]) "Failed receipt query changed hash."
          return failedChain
        throw <| IO.userError "Unexpected failed RPC request."
    require ((← inspectWith status "rpc" "bundler" failed).status == .failed)
      "Exact failed EntryPoint event was not reported failed."
    let pending : String → JsonRpc.Method → Array Json → IO Json :=
      fun url method params => do
        if url == "rpc" && method == .getTransactionReceipt then return .null
        success url method params
    require ((← inspectWith status "rpc" "bundler" pending).status == .pending)
      "Missing receipt was not pending."
    let wrongChain : String → JsonRpc.Method → Array Json → IO Json :=
      fun url method params => do
        if url == "rpc" && method == .chainId then return toJson ("0xaa" : String)
        success url method params
    require ((← inspectWith status "rpc" "bundler" wrongChain).status == .unknown)
      "Wrong-chain RPC produced a definite status."
    let noBundler : String → JsonRpc.Method → Array Json → IO Json :=
      fun url method params => do
        if url == "bundler" then throw <| IO.userError "Bundler unavailable"
        if method == .chainId then return toJson ("0x1" : String)
        if method == .getLogs then
          return Json.arr #[ (← field chain "logs").getArr?.toOption.get![0]! ]
        if method == .getTransactionReceipt then
          require (params == #[toJson txHash]) "Fallback changed transaction hash."
          return chain
        throw <| IO.userError "Unexpected chain-log fallback request."
    require ((← inspectWith status "rpc" "bundler" noBundler).status == .confirmed)
      "Exact EntryPoint log fallback did not confirm chain evidence."
    let savedHashOnly : String → JsonRpc.Method → Array Json → IO Json :=
      fun url method params => do
        if url == "bundler" then throw <| IO.userError "Bundler unavailable"
        if method == .chainId then return toJson ("0x1" : String)
        if method == .getLogs then throw <| IO.userError "Log index unavailable"
        if method == .getTransactionReceipt then
          require (params == #[toJson txHash]) "Saved receipt query changed transaction hash."
          return chain
        throw <| IO.userError "Unexpected saved-hash RPC request."
    require ((← inspectWith { status with transactionHash := some txHash }
      "rpc" "bundler" savedHashOnly).status == .confirmed)
      "A saved transaction hash was not reconciled when indexes were unavailable."
    let wrongReceipt : String → JsonRpc.Method → Array Json → IO Json :=
      fun url method params => do
        if url == "rpc" && method == .getTransactionReceipt then
          return chain.setObjVal! "transactionHash" (toJson failedTxHash)
        success url method params
    require ((← inspectWith status "rpc" "bundler" wrongReceipt).status == .unknown)
      "Mismatched transaction receipt was confirmed."
    IO.println "PASS: one-note withdrawal status confirmation, failure, pending, fallback, and wrong-evidence checks"
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)

end Tornado.Cli.WithdrawalStatusCommand.Test

def main : IO UInt32 := Tornado.Cli.WithdrawalStatusCommand.Test.main
