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

private def failureMessage (action : IO α) : IO String := do
  try
    let _ ← action
    return ""
  catch error => return error.toString

private def rejected (reply : JsonRpc.Reply) (params : Array Json := #[]) : Bool :=
  match classifyEstimate reply params with | .rejected => true | _ => false

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
  | opaqueError | malformed | failed | wrongChain | knownEstimatorError
  deriving BEq

private def simulationCase (operation : UserOperation) (expected : List Events.ExpectedWithdrawal)
    (response : Json) (fault : SimulationFault) (policy : Policy) (prior : Estimation)
    (bounds : Bundler.Bounds := {}) :
    IO (Bool × Bool × Nat) := do
  let requests ← IO.mkRef (0 : Nat)
  let simulations ← IO.mkRef (0 : Nat)
  let transport : Transport := {
    call := fun url id method params => do
      requests.modify (· + 1)
      require (id == (← requests.get)) "Network request IDs were reused."
      require (url == "https://simulation.example.test") "Signed simulation used another endpoint."
      match method with
      | .chainId => return .success <| toJson (if fault == .wrongChain then "0xaa36a7" else "0x1")
      | .simulateV1 =>
        require (params == (← checked <| EntryPointSimulation.requestParams operation bounds))
          "Signed simulation request changed the reviewed bounds or operation."
        simulations.modify (· + 1)
        if fault == .transport then throw <| IO.userError "HTTPS transport unavailable"
        if fault == .knownEstimatorError then
          let argument := Bundler.dataHex (← checked <| Abi.uintWord 20000000)
          return .failure (-32501) ("AA33 reverted 0x54107e37" ++
            String.ofList (argument.toList.drop 2)) none
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
  let first ← client.simulate operation expected prior bounds
  let second ← client.simulate operation expected prior bounds
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
    ("callData", toJson ("0x" : String)), ("callGasLimit", toJson ("0x0" : String)),
    ("signature", toJson (Bundler.dataHex (← checked PaymasterPrepare.dummySignature))),
    ("paymasterData", toJson (Bundler.dataHex sponsor))]
  return #[operation, toJson (← checked <| Bundler.address Bundler.entryPoint), Json.mkObj []]

private inductive GasReadFault where
  | twiceTransport | alwaysTransport | tls | remoteRejected | malformed | crossMethodRecovery
  deriving BEq

private def gasReadCase (fault : GasReadFault) : IO (String × Array Nat × Array JsonRpc.Method) := do
  let calls ← IO.mkRef (#[] : Array JsonRpc.Method)
  let waits ← IO.mkRef (#[] : Array Nat)
  let transport : Transport := {
    call := fun url id method _ => do
      require (url == settings.rpcUrl) "Gas refresh changed the configured RPC."
      calls.modify (·.push method)
      let methods ← calls.get
      require (id == methods.size) "A gas refresh retry reused its request ID."
      if fault == .alwaysTransport ||
          (fault == .twiceTransport && methods.size <= 2) ||
          (fault == .crossMethodRecovery && (methods.size == 1 || methods.size == 3)) then
        throw <| IO.userError "HTTPS transport unavailable"
      if fault == .tls then throw <| IO.userError "HTTPS request rejected or exceeded bounds"
      if fault == .remoteRejected then
        return .failure (-32000) "UNTRUSTED_PROVIDER_DETAIL_SENTINEL" none
      if fault == .malformed then
        return .success <| toJson ("UNTRUSTED_PROVIDER_DETAIL_SENTINEL" : String)
      match method with
      | .feeHistory =>
        if fault == .crossMethodRecovery then return .success <| Json.mkObj []
        return .success <| Json.mkObj [
          ("baseFeePerGas", toJson #["0x12a05f200", "0x12a05f200"]),
          ("reward", toJson #[#["0xb2d05e00"]])]
      | .getBlockByNumber =>
        return .success <| Json.mkObj [("baseFeePerGas", toJson ("0x12a05f200" : String))]
      | .maxPriorityFee => return .success <| toJson ("0xb2d05e00" : String)
      | _ => throw <| IO.userError "Gas refresh requested a non-reference method."
    nowMs := pure 0
    sleepMs := fun ms => waits.modify (·.push ms) }
  let client ← createWith settings transport
  let error ← failureMessage <| client.revalidateGasPrice { maxFee := 16000000000, priority := 6000000000 }
  return (error, ← waits.get, ← calls.get)

private def downwardCase (original : SponsoredWithdrawal.Gas)
    (maximum priority base tip : Nat) (custom : Bool := false)
    (badQuote : Bool := false) : IO (Option SponsoredWithdrawal.Gas × String × Array JsonRpc.Method) := do
  let calls ← IO.mkRef (#[] : Array JsonRpc.Method)
  let transport : Transport := {
    call := fun url id method _ => do
      calls.modify (·.push method)
      require (id == (← calls.get).size) "A downward bid refresh reused a request ID."
      match method with
      | .pimlicoGasPrice =>
        require (!custom && url == settings.bundlerUrl) "A custom bundler consulted the third-party price oracle."
        if badQuote then return .success <| toJson ("UNTRUSTED_PROVIDER_DETAIL_SENTINEL" : String)
        return .success <| Json.mkObj [("standard", Json.mkObj [
          ("maxFeePerGas", toJson (Bundler.quantity maximum)),
          ("maxPriorityFeePerGas", toJson (Bundler.quantity priority))])]
      | .feeHistory =>
        require (url == settings.rpcUrl) "Downward gas refresh changed the selected host RPC."
        let value := Bundler.quantity base
        return .success <| Json.mkObj [
          ("baseFeePerGas", toJson #[value, value]),
          ("reward", toJson #[#[Bundler.quantity tip]])]
      | _ => throw <| IO.userError "Downward refresh attempted a non-price request."
    nowMs := pure 0 }
  let client ← createWith { settings with customBundler := custom } transport
  try
    let gas ← client.refreshGasBidDownward original {}
    return (some gas, "", ← calls.get)
  catch error => return (none, error.toString, ← calls.get)

set_option maxRecDepth 4096 in
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
  let validationOnly ← dummyParams
  require (Bundler.dataHex (Abi.selector "CallGasLimitNonZero(uint256)") == "0x54107e37")
    "Known estimator custom-error selector differs from its ABI signature."
  let argument := Bundler.dataHex (← checked <| Abi.uintWord 20000000)
  let revert := "0x54107e37" ++ String.ofList (argument.toList.drop 2)
  let errorText := "UserOperation reverted during simulation with reason: AA33 reverted " ++ revert
  let known : JsonRpc.Reply := .failure (-32501) errorText none
  match classifyEstimate known validationOnly with
  | .unavailable .validationOnlyEstimator => pure ()
  | _ => throw <| IO.userError "Observed validation-only estimator incompatibility was not recognized."
  require (rejected known) "Estimator incompatibility was admitted without zero-execution context."
  let zero := "0x54107e37" ++ String.ofList (List.replicate 64 '0')
  for (message, code, data) in [
      ("AA33 reverted " ++ zero, (-32501 : Int), (none : Option Json)),
      ("AA33 reverted " ++ String.ofList (revert.toList.dropLast), -32501, none),
      ("AA33 reverted " ++ revert ++ "0", -32501, none),
      ("AA33 reverted junk" ++ revert, -32501, none),
      ("AA33 reverted 0xdeadbeef" ++ String.ofList (List.replicate 64 '1'), -32501, none),
      ("AA23 reverted " ++ revert, -32501, none),
      (errorText, -32603, none),
      (errorText, -32501, some (toJson ("0xdead" : String)))] do
    require (rejected (.failure code message data) validationOnly)
      "Unrelated, malformed or data-bearing rejection became validation-only fallback."
  for operation in [
      validationOnly[0]!.setObjVal! "callGasLimit" (toJson ("0x1" : String)),
      validationOnly[0]!.setObjVal! "callData" (toJson ("0x1234" : String)),
      validationOnly[0]!.setObjVal! "callGasLimit" (toJson ("0x00" : String))] do
    require (rejected known (validationOnly.set! 0 operation))
      "Execution-bearing or noncanonical operation acquired validation-only fallback."
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
  let deploymentOperation := { operation with verificationGasLimit := 1450271 }
  let (defaultAllowed, _, defaultCount) ← simulationCase deploymentOperation expected response
    .unsupported .bestEffort .estimated
  require (!defaultAllowed && defaultCount == 0)
    "Default simulation bounds admitted deployment gas above one million."
  let deploymentBounds : Bundler.Bounds := { maxVerificationGas := 2000000 }
  let (scopedAllowed, scopedRepeated, scopedCount) ← simulationCase deploymentOperation expected response
    .unsupported .bestEffort .estimated deploymentBounds
  require (scopedAllowed && !scopedRepeated && scopedCount == 1)
    "Reviewed deployment bounds were lost before simulation or allowed repeated exposure."
  let (overScoped, _, overScopedCount) ← simulationCase
    { deploymentOperation with verificationGasLimit := 2000001 } expected response
    .unsupported .bestEffort .estimated deploymentBounds
  require (!overScoped && overScopedCount == 0)
    "Scoped simulation bounds admitted verification gas above two million."
  for fault in #[SimulationFault.unsupported, .transport] do
    let (allowed, second, count) ← simulationCase operation expected response fault .bestEffort .estimated
    require (allowed && !second && count == 1)
      "Explicit best-effort policy failed a known outage or repeated signed exposure."
    let (required, _, _) ← simulationCase operation expected response fault .required .estimated
    require (!required) "Required signed simulation admitted an outage."
    let (fallback, _, _) ← simulationCase operation expected response fault .bestEffort (.fallback .transport)
    require (!fallback) "Unavailable simulation was admitted after fallback gas estimation."
  for fault in #[SimulationFault.tls, .explicitFailure, .errorData, .opaqueError,
      .malformed, .failed, .wrongChain, .knownEstimatorError] do
    let (allowed, repeated, _) ← simulationCase operation expected response fault .bestEffort .estimated
    require (!allowed && !repeated) "A known signed simulation failure was admitted or retried."
  let ids ← IO.mkRef (#[] : Array Nat)
  let oracleReads ← IO.mkRef (0 : Nat)
  let estimateCalls ← IO.mkRef (0 : Nat)
  let estimateReply ← IO.mkRef (JsonRpc.Reply.failure (-32603) "Opaque internal error" none)
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
        estimateReply.get
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
  let lowered := { gas with maxFee := 12000000000, priority := 3000000000 }
  require ((acceptDownwardGas gas lowered).isOk &&
    SponsoredWithdrawal.ethFee lowered <= SponsoredWithdrawal.ethFee gas)
    "A componentwise lower bid failed the fixed-limit or prefund monotonicity checks."
  for changed in [
      { lowered with verification := lowered.verification + 1 },
      { lowered with execution := lowered.execution + 1 },
      { lowered with preVerification := lowered.preVerification + 1 },
      { lowered with paymasterVerification := lowered.paymasterVerification + 1 },
      { lowered with postOp := lowered.postOp + 1 },
      { lowered with maxFee := gas.maxFee + 1 },
      { lowered with priority := gas.priority + 1 },
      { lowered with maxFee := 0 },
      { lowered with maxFee := lowered.priority - 1 }] do
    require (!(acceptDownwardGas gas changed).isOk)
      "A downward gas gate admitted a changed limit, increased price or invalid fee pair."
  require (!(acceptDownwardGas gas lowered { maxGasCostWei := 1 }).isOk)
    "A downward gas gate ignored the configured maximum gas cost."
  let oldTiny : SponsoredWithdrawal.Gas := { maxFee := 3001000026, priority := 3000000000 }
  let (freshTiny, error, calls) ← downwardCase oldTiny 5775027 5775001 13 999999987
  require (error.isEmpty && freshTiny.isSome && freshTiny.get!.maxFee == 6775027 &&
    freshTiny.get!.priority == 5775001 && (acceptDownwardGas oldTiny freshTiny.get!).isOk &&
    calls == #[JsonRpc.Method.pimlicoGasPrice, .feeHistory])
    "A lower fresh quote could not recover the exact tiny-fee host-cap drift within the old budget."
  let (custom, error, calls) ← downwardCase gas 0 0 5000000000 3000000000 true
  require (custom.isSome && error.isEmpty && custom.get!.maxFee == gas.maxFee &&
    custom.get!.priority == gas.priority && calls == #[JsonRpc.Method.feeHistory])
    "Custom downward refresh changed host-only price synthesis."
  let (clipped, error, _) ← downwardCase { gas with maxFee := 6000000000, priority := 1000000000 }
    16000000000 1000000000 5000000000 3000000000
  require (clipped.isSome && error.isEmpty && clipped.get!.maxFee == 6000000000 &&
    clipped.get!.priority == 1000000000)
    "A fresh maximum above the old maximum was not safely retained at a still-covering old ceiling."
  let (uncovered, error, _) ← downwardCase { gas with maxFee := 5999999999, priority := 1000000000 }
    16000000000 1000000000 5000000000 3000000000
  require (uncovered.isNone && error.contains "cannot fit the prepared budget")
    "A downward refresh accepted a bid that no longer covers current base plus priority."
  let (higherPriority, error, _) ← downwardCase { gas with priority := 1000000000 }
    16000000000 2000000000 5000000000 3000000000
  require (higherPriority.isNone && error.contains "recommended priority fee exceeds the prepared bid")
    "A higher fresh recommended priority was silently lowered or raised beyond the prepared bid."
  let (badRaw, error, _) ← downwardCase gas 100000000000 3000000000 5000000000 3000000000
  require (badRaw.isNone && error.contains "fresh bundler gas quote exceeds current price limits")
    "A raw invalid fresh quote was repaired by clipping instead of rejected first."
  let (badShape, error, _) ← downwardCase gas 12000000000 3000000000 5000000000 3000000000 false true
  require (badShape.isNone && error.contains "fresh bundler gas quote is malformed" &&
    !error.contains "UNTRUSTED_PROVIDER_DETAIL_SENTINEL")
    "Malformed fresh quote details reached the caller."
  client.revalidateGasPrice gas
  let highQuote ← failureMessage <| client.revalidateGasPrice { gas with maxFee := 100000000000 }
  require (highQuote.contains "Prepared gas quote exceeds current network price limits" &&
    highQuote.contains "current base 5000000000" &&
    highQuote.contains "reference priority 3000000000" &&
    highQuote.contains "prepared maxFee 100000000000" &&
    highQuote.contains "prepared priority 6000000000")
    "An excessive gas quote passed revalidation or hid its bounded fee details."
  let lowQuote ← failureMessage <| client.revalidateGasPrice
    { gas with maxFee := 5000000000, priority := 1000000000 }
  require (lowQuote.contains "Prepared max fee no longer covers the current base fee and priority fee" &&
    lowQuote.contains "prepared maxFee 5000000000" &&
    lowQuote.contains "prepared priority 1000000000")
    "An insufficient gas quote passed revalidation or lacked fresh-quote guidance."
  let (recovered, waits, calls) ← gasReadCase .twiceTransport
  require (recovered.isEmpty && waits == #[500, 1000] &&
    calls == #[JsonRpc.Method.feeHistory, .feeHistory, .feeHistory])
    "Transient gas-reference reads did not recover within two bounded backoffs."
  let (crossRecovered, waits, calls) ← gasReadCase .crossMethodRecovery
  require (crossRecovered.isEmpty && waits == #[500, 1000] && calls.size == 5)
    "Gas-reference fallback reset the shared two-retry budget or lost existing fallback semantics."
  let (unavailable, waits, calls) ← gasReadCase .alwaysTransport
  require (unavailable == "Could not refresh network gas prices. Check --rpc or try another endpoint." &&
    waits == #[500, 1000] && calls.size == 4)
    "Persistent gas-reference transport failure exceeded two total backoffs or lost its RPC guidance."
  for fault in [GasReadFault.tls, .remoteRejected, .malformed] do
    let (error, waits, calls) ← gasReadCase fault
    require (error == "Could not refresh network gas prices. Check --rpc or try another endpoint." &&
      !error.contains "UNTRUSTED_PROVIDER_DETAIL_SENTINEL" && waits.isEmpty && calls.size == 2)
      "TLS, remote rejection or malformed fee data was retried or reflected provider text."
  let tinyBase ← IO.mkRef (20 : Nat)
  let tinyTransport : Transport := {
    call := fun _ _ method _ => do
      require (method == .feeHistory) "Tiny-base revalidation changed its RPC read."
      let base := Bundler.quantity (← tinyBase.get)
      return .success <| Json.mkObj [
        ("baseFeePerGas", toJson #[base, base]),
        ("reward", toJson #[#[Bundler.quantity 500000000]])]
    nowMs := pure 0 }
  let tinyClient ← createWith settings tinyTransport
  let paddedGas : SponsoredWithdrawal.Gas := { maxFee := 1156000019, priority := 1155000000 }
  tinyClient.revalidateGasPrice paddedGas
  tinyBase.set 1000020
  let exhausted ← failureMessage <| tinyClient.revalidateGasPrice paddedGas
  require (exhausted.contains "Prepared max fee no longer covers" &&
    exhausted.contains "current base 1000020" &&
    exhausted.contains "prepared maxFee 1156000019")
    "Initial tiny-base headroom bypassed later expiry instead of requiring a fresh proof-bound quote."
  let params ← dummyParams
  match ← client.estimate params with
  | .unavailable .bundlerInternal => pure ()
  | _ => throw <| IO.userError "Structured estimator reply classification changed."
  estimateReply.set known
  match ← client.estimate params with
  | .unavailable .validationOnlyEstimator => pure ()
  | _ => throw <| IO.userError "Live adapter dropped the operation context for known estimator incompatibility."
  let changed := params.set! 0 (params[0]!.setObjVal! "signature" (toJson (Bundler.dataHex operation.signature)))
  match ← client.estimate changed with
  | .rejected => pure ()
  | _ => throw <| IO.userError "A non-dummy signature reached estimation."
  require ((← estimateCalls.get) == 2) "Malformed dummy request reached the network."
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
