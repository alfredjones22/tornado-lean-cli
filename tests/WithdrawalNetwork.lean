import Tornado.Cli.WithdrawalNetwork

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Cli.PaymasterPrepare
open Tornado.Cli.WithdrawalNetwork
open Tornado.Cli

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def rejects (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def rejected (reply : JsonRpc.Reply) : Bool :=
  match classifyEstimate reply with | .rejected => true | _ => false

private def settings : Settings := {
  chainId := 1
  rpcUrl := "https://rpc.example.test"
  bundlerUrl := "https://bundler.example.test"
  simulationRpcUrl := some "https://simulation.example.test" }

private def fixtureOperation : IO UserOperation := do
  let signature ← checked <| parseHexBytes ("0x" ++ String.ofList (List.replicate 128 '1') ++ "1b")
  return {
    sender := 1, nonce := 0, callData := ← checked (parseHexBytes "0x1234"),
    verificationGasLimit := 50000, callGasLimit := 100000, preVerificationGas := 100000,
    maxFeePerGas := 1000000000, maxPriorityFeePerGas := 100000000,
    paymaster := some 0xb0ffcdc890e969579d348f519a9c3920c2dd04a5,
    paymasterVerificationGasLimit := 450000, paymasterPostOpGasLimit := 50000,
    paymasterData := ← checked (parseHexBytes "0x1234"), signature }

private def expectedWithdrawal : IO (List Events.ExpectedWithdrawal) := do
  return [{
    pool := 0x199112eb461ea7eec1d75b33343542e1d069b41c
    recipient := 2
    nullifierHash := ← checked <| Abi.uintWord 7
    relayer := 0xb0ffcdc890e969579d348f519a9c3920c2dd04a5
    fee := 1 }]

private inductive SimulationFault where
  | none | unsupported | transport | tls | explicitFailure | errorData
  | opaqueError | malformed | failed | wrongChain
  deriving BEq

private def simulationCase (operation : UserOperation) (expected : List Events.ExpectedWithdrawal)
    (response : Json) (fault : SimulationFault) (policy : Policy) (prior : Estimation) :
    IO (Bool × Bool × Nat) := do
  let requests ← IO.mkRef (0 : Nat)
  let simulations ← IO.mkRef (0 : Nat)
  let transport : Transport := {
    call := fun url id method _ => do
      requests.modify (· + 1)
      require (id == (← requests.get)) "Network request IDs were reused."
      require (url == "https://simulation.example.test") "Signed simulation used another endpoint."
      match method with
      | .chainId => return .success <| toJson (if fault == .wrongChain then "0xaa36a7" else "0x1")
      | .simulateV1 =>
        simulations.modify (· + 1)
        if fault == .transport then throw <| IO.userError "HTTPS transport unavailable"
        if fault == .tls then throw <| IO.userError "HTTPS request rejected or exceeded bounds"
        if fault == .unsupported then return .failure (-32601) "Method not found" none
        if fault == .explicitFailure then return .failure (-32601) "AA23 execution reverted" none
        if fault == .errorData then return .failure (-32601) "Method not found" (some (toJson ("0xdead" : String)))
        if fault == .opaqueError then return .failure (-32603) "Opaque internal error" none
        if fault == .malformed then return .success (Json.arr #[])
        if fault == .failed then
          let blocks ← checked response.getArr?
          let calls ← checked <| (← checked <| blocks[0]!.getObjVal? "calls").getArr?
          let failedCall := calls[0]!.setObjVal! "status" (toJson ("0x0" : String))
          return .success (Json.arr #[blocks[0]!.setObjVal! "calls" (Json.arr #[failedCall])])
        return .success response
      | _ => throw <| IO.userError "Unexpected signed simulation fixture method"
    nowMs := pure 0 }
  let client ← createWith { settings with simulationPolicy := policy } transport
  let first ← client.simulate operation expected prior
  let second ← client.simulate operation expected prior
  return (first, second, ← simulations.get)

private def dummyParams : IO (Array Json) := do
  let sponsor ← checked <| Abi.sponsorParameters {
    instanceAddress := 1
    proof := ← checked PaymasterPrepare.dummyProof
    root := ← checked <| Abi.uintWord 2
    nullifierHash := ← checked <| Abi.uintWord 3
    recipient := 4
    fee := 5 }
  let operation := Json.mkObj [
    ("signature", toJson (Bundler.dataHex (← checked PaymasterPrepare.dummySignature))),
    ("paymasterData", toJson (Bundler.dataHex sponsor))]
  return #[operation, toJson (← checked <| Bundler.address Bundler.entryPoint), Json.mkObj []]

def main : IO UInt32 := do
  require (transportUnavailable (IO.userError "HTTPS transport unavailable") &&
    !transportUnavailable (IO.userError "HTTPS transport unavailable: secret") &&
    !transportUnavailable (IO.userError "HTTPS request rejected or exceeded bounds"))
    "Arbitrary failures were classified as a transport outage."
  match classifyEstimate (.failure (-32603) "Opaque internal error" none) with
  | .unavailable .bundlerInternal => pure ()
  | _ => throw <| IO.userError "Opaque estimator internal outage was not classified."
  match classifyEstimate (.failure (-32521) "AA95 execution out of gas" none) with
  | .executionOutOfGas => pure ()
  | _ => throw <| IO.userError "Explicit bounded execution OOG was not classified."
  for reply in #[
      JsonRpc.Reply.failure (-32603) "AA23 reverted" none,
      .failure (-32603) "Unknown" (some (toJson ("0xdead" : String))),
      .failure (-32521) "AA95 out of gas during verification" none,
      .failure (-32521) "AA95 execution out of gas" (some (toJson ("0x" : String))),
      .failure (-32603) "execution out of gas" none,
      .failure (-32601) "Method not found" none] do
    require (rejected reply) "A known validation/revert failure became estimator fallback."
  let fixture ← checked <| Json.parse (← IO.FS.readFile "fixtures/entrypoint-simulation.json")
  let response ← checked <| fixture.getObjVal? "response"
  let operation ← fixtureOperation
  let expected ← expectedWithdrawal
  let (passed, repeated, count) ← simulationCase operation expected response .none .required .estimated
  require (passed && !repeated && count == 1)
    "Exact signed simulation failed or was exposed more than once."
  for fault in #[SimulationFault.unsupported, .transport] do
    let (allowed, second, count) ← simulationCase operation expected response fault .bestEffort .estimated
    require (allowed && !second && count == 1)
      "Explicit best-effort policy failed a known outage or repeated signed exposure."
    let (required, _, _) ← simulationCase operation expected response fault .required .estimated
    require (!required) "Required signed simulation admitted an outage."
    let (fallback, _, _) ← simulationCase operation expected response fault .bestEffort (.fallback .transport)
    require (!fallback) "Unavailable simulation was admitted after fallback gas estimation."
  for fault in #[SimulationFault.tls, .explicitFailure, .errorData, .opaqueError, .malformed, .failed, .wrongChain] do
    let (allowed, repeated, _) ← simulationCase operation expected response fault .bestEffort .estimated
    require (!allowed && !repeated) "A known signed simulation failure was admitted or retried."
  let ids ← IO.mkRef (#[] : Array Nat)
  let oracleReads ← IO.mkRef (0 : Nat)
  let estimateCalls ← IO.mkRef (0 : Nat)
  let sendCalls ← IO.mkRef (0 : Nat)
  let transport : Transport := {
    call := fun _ id method _ => do
      ids.modify (·.push id)
      match method with
      | .chainId => return .success <| toJson ("0x1" : String)
      | .blockNumber => return .success <| toJson ("0x64" : String)
      | .getTransactionCount => return .success <| toJson ("0x7" : String)
      | .feeHistory => return .success <| Json.mkObj [
        ("baseFeePerGas", toJson #["0x77359400", "0x12a05f200", "0x1dcd65000"]),
        ("reward", toJson #[#["0x3b9aca00"], #["0xb2d05e00"]])]
      | .pimlicoGasPrice =>
        oracleReads.modify (· + 1)
        throw <| IO.userError "Custom price must not use the bundler oracle"
      | .estimateUserOperationGas =>
        estimateCalls.modify (· + 1)
        return .failure (-32603) "Opaque internal error" none
      | .sendUserOperation =>
        sendCalls.modify (· + 1)
        return .success <| toJson ("0x" ++ String.ofList (List.replicate 64 '1'))
      | .call => return .failure (-32000) "secret remote provider details" none
      | _ => throw <| IO.userError "Unexpected public network fixture method"
    nowMs := pure 0 }
  let client ← createWith { settings with customBundler := true } transport
  client.checkChain
  require ((← client.blockNumber) == 100 && (← client.nonce 1) == 7)
    "Bounded chain/block/nonce helpers changed."
  let prices ← client.bundler .pimlicoGasPrice #[]
  let standard ← checked <| prices.getObjVal? "standard"
  let maximum ← checked <| JsonRpc.parseHexQuantity (← checked <| (← checked <| standard.getObjVal? "maxFeePerGas").getStr?)
  let priority ← checked <| JsonRpc.parseHexQuantity (← checked <| (← checked <| standard.getObjVal? "maxPriorityFeePerGas").getStr?)
  require (maximum == 16000000000 && priority == 6000000000 && (← oracleReads.get) == 0)
    "Custom bundler fee synthesis used another oracle or wrong host bounds."
  let gas : SponsoredWithdrawal.Gas := { maxFee := 16000000000, priority := 6000000000 }
  client.revalidateGasPrice gas
  require (← rejects <| client.revalidateGasPrice { gas with maxFee := 100000000000 })
    "A stale excessive gas price passed final revalidation."
  require (← rejects <| client.revalidateGasPrice
    { gas with maxFee := 5000000000, priority := 1000000000 })
    "An insufficient gas price passed final revalidation."
  let params ← dummyParams
  match ← client.estimate params with
  | .unavailable .bundlerInternal => pure ()
  | _ => throw <| IO.userError "Structured estimator reply classification changed."
  let changed := params.set! 0 (params[0]!.setObjVal! "signature" (toJson (Bundler.dataHex operation.signature)))
  match ← client.estimate changed with
  | .rejected => pure ()
  | _ => throw <| IO.userError "A non-dummy signature reached estimation."
  require ((← estimateCalls.get) == 1) "Malformed dummy request reached the network."
  let sendParams := #[params[0]!, params[1]!]
  let _ ← client.send .sendUserOperation sendParams
  require (← rejects <| client.send .sendUserOperation sendParams)
    "The same public operation was sent twice by one adapter."
  require ((← sendCalls.get) == 1) "A duplicate send reached transport."
  require (← rejects <| client.rpc .sendUserOperation #[])
    "Read-only adapter exposed a send method."
  require (← rejects <| client.send .sendRawTransaction #[])
    "Bundler adapter accepted an unrelated send method."
  let remoteError ← try
    let _ ← client.rpc .call #[]
    pure ""
    catch error => pure error.toString
  require (remoteError == "Withdrawal network request failed or was rejected.")
    "A remote error or secret provider details escaped to the caller."
  let usedIds ← ids.get
  for i in [0:usedIds.size] do
    require (usedIds[i]! == i + 1) "Network request IDs were not fresh."
  IO.println "PASS: structured estimation errors, bounded native fees, one-attempt simulation/send, and outage admission policy"
  return 0
