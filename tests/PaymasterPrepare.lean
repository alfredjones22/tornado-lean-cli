import Tornado.Cli.PaymasterPrepare

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire Tornado.Protocol.SponsoredWithdrawal
open Tornado.Cli.PaymasterPrepare

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def field (value : Json) (name : String) : IO Json :=
  checked <| value.getObjVal? name

private def qty (value : Json) : IO Nat := do
  checked <| JsonRpc.parseHexQuantity (← checked value.getStr?)

private def word (value : Nat) : IO Json :=
  return toJson (Bundler.dataHex (← checked <| Abi.uintWord value))

private def inputFor (token : Bool := false) (batch : Bool := false) : IO Input := do
  let some pool := if token then poolFor .mainnet "100" "USDC"
      else poolFor .mainnet "0.01" "ETH"
    | throw <| IO.userError "Missing public fixture pool."
  let poolBytes ← checked <| parseHexBytes pool.address
  let poolAddress := poolBytes.data.foldl (fun n b => n * 256 + b.toNat) 0
  let request : Request := {
    chainId := 1, pool := poolAddress, commitment := 42, nullifierHash := 43,
    leafIndex := 0, root := 44, siblings := Array.replicate 20 0,
    pathIndices := Array.replicate 20 0, recipient := 2, relayer := 0, fee := 0, refund := 0 }
  let notes := if batch then #[request, { request with commitment := 45, nullifierHash := 46 }]
    else #[request]
  let mode := if batch then Mode.batch ⟨3, 4, 0, true⟩ 5 #[] else .single 1 2
  return { notes, mode, checkedBlock := 100 }

private inductive Fault where
  | none | growOnce | unstable | aboveGasCap | aboveCallCap | rejected | unavailable
  | internalUnavailable | validationOnlyEstimator | outOfGasOnce | outOfGasAlways | badRandom
  | staleHead | wrongChain | emptyVerifier | highPrice | zeroQuote | consumingQuote
  | malformedFeeHistory | malformedEstimate
  | omitPaymasterGas | omitPaymasterVerification | omitPostOp | omitPaymasterGrowOnce
  | zeroPaymasterGas | malformedPaymasterGas
  | undeployedVerificationEstimate
  | tinyBase | tinyBaseFullCap | tinyBaseInvalidQuote | thresholdBase
  deriving BEq

private structure Run where
  quote : Option Quote
  estimates : Nat
  proofs : Nat
  histories : Nat
  tokenQuotes : Nat
  error : Bool
  errorText : String := ""

private def scenario (input : Input) (fault : Fault := .none)
    (makeProof : Bool := false) : IO Run := do
  let estimates ← IO.mkRef (0 : Nat)
  let proofs ← IO.mkRef (0 : Nat)
  let histories ← IO.mkRef (0 : Nat)
  let tokenQuotes ← IO.mkRef (0 : Nat)
  let random ← IO.mkRef (1000 : Nat)
  let effects : Effects := {
    rpc := fun method params => do
      match method with
      | .chainId => return toJson (if fault == .wrongChain then "0xaa36a7" else "0x1")
      | .blockNumber => return toJson (if fault == .staleHead then "0xc8" else "0x64")
      | .feeHistory =>
        if fault == .malformedFeeHistory then return Json.mkObj []
        let tiny := [Fault.tinyBase, .tinyBaseFullCap, .tinyBaseInvalidQuote].contains fault
        let base := if tiny then Bundler.quantity 14
          else if fault == .thresholdBase then Bundler.quantity 1000000 else "0x3b9aca00"
        let tip := if tiny then Bundler.quantity 500000000 else "0x3b9aca00"
        return Json.mkObj [
          ("baseFeePerGas", toJson #[base, base]),
          ("reward", toJson #[#[tip]])]
      | .getBlockByNumber => return Json.mkObj [("baseFeePerGas", toJson ("0x3b9aca00" : String))]
      | .maxPriorityFee => return toJson ("0x3b9aca00" : String)
      | .call =>
        let payload ← checked <| parseHexBytes
          (← checked <| (← field params[0]! "data").getStr?)
        if payload == Abi.selector "verifier()" then return (← word 0x9999)
        require (payload.extract 0 4 == Abi.selector "quoteWeiInToken(address,uint256)")
          "Unexpected preparation contract read."
        tokenQuotes.modify (· + 1)
        return (← word (if fault == .zeroQuote then 0
          else if fault == .consumingQuote then 100000000 else 1000))
      | .getCode => return toJson (if fault == .emptyVerifier then "0x" else "0x60006000")
      | _ => throw <| IO.userError "Unexpected host RPC in public estimation fixture"
    bundler := fun method _ => do
      require (method == .pimlicoGasPrice) "Preparation called a money-moving bundler method."
      let tiny := [Fault.tinyBase, .tinyBaseFullCap, .tinyBaseInvalidQuote].contains fault
      let maximum := if fault == .tinyBase then Bundler.quantity 1155000019
        else if fault == .tinyBaseFullCap then Bundler.quantity 2000000042
        else if fault == .tinyBaseInvalidQuote then Bundler.quantity 2000000043
        else if fault == .highPrice then "0xe8d4a51000" else "0xb2d05e00"
      let priority := if tiny then Bundler.quantity 1155000000 else "0x3b9aca00"
      return Json.mkObj [("standard", Json.mkObj [
        ("maxFeePerGas", toJson maximum),
        ("maxPriorityFeePerGas", toJson priority)])]
    estimate := fun params => do
      estimates.modify (· + 1)
      require ((← proofs.get) == 0) "Real proofs were requested before estimation finished."
      require (params.size == 3) "Estimation omitted verifier state overrides."
      let operation := params[0]!
      require ((← checked <| (← field operation "signature").getStr?) ==
        Bundler.dataHex (← checked dummySignature)) "Estimation used a real owner signature."
      let sponsorBytes ← checked <| parseHexBytes
        (← checked <| (← field operation "paymasterData").getStr?)
      let sponsor ← checked <| Abi.decodeSponsorParameters sponsorBytes
      require (sponsor.proof == (← checked dummyProof)) "Estimation used a real proof."
      let nullifier := sponsor.nullifierHash.data.foldl (fun n b => n * 256 + b.toNat) 0
      require (!(input.notes.any (fun note => note.nullifierHash == nullifier)))
        "Estimation disclosed a selected note nullifier hash."
      let verifierText ← checked <| Bundler.address 0x9999
      let shadowText ← checked <| Bundler.address 0x4b6f68616b75
      let overrideCode ← checked <| (← field (← field params[2]! shadowText) "code").getStr?
      require (overrideCode == "0x60006000" && (params[2]!.getObjVal? verifierText).isOk)
        "State overrides lost the original verifier or its forwarding shim."
      match input.mode with
      | .single .. =>
        let auth ← field operation "eip7702Auth"
        require ((← checked <| (← field auth "nonce").getStr?) == "0x0")
          "Dummy direct authorization changed nonce."
      | .batch .. => do
        require (!(operation.getObjVal? "eip7702Auth").isOk)
          "Batch estimation unexpectedly included owner authorization."
      if fault == .rejected then return .rejected
      if fault == .unavailable then return .unavailable .transport
      if fault == .internalUnavailable then return .unavailable .bundlerInternal
      if fault == .validationOnlyEstimator then return .unavailable .validationOnlyEstimator
      if fault == .outOfGasAlways || (fault == .outOfGasOnce && (← estimates.get) == 1) then
        return .executionOutOfGas
      if fault == .malformedEstimate then return .estimated <| Json.mkObj [
        ("providerDetails", toJson ("UNTRUSTED_PROVIDER_DETAIL_SENTINEL" : String))]
      let stable (name : String) : IO Json := do
        let current ← qty (← field operation name)
        if fault == .undeployedVerificationEstimate && name == "verificationGasLimit" then
          return toJson (Bundler.quantity 1208559)
        let value := if fault == .unstable ||
            ((fault == .growOnce || fault == .omitPaymasterGrowOnce) &&
              (← estimates.get) == 1 && name == "verificationGasLimit") then current
          else current * 10 / 12
        return toJson (Bundler.quantity value)
      let paymasterGas ← if fault == .aboveGasCap then pure <| toJson ("0x1e8480" : String)
        else stable "paymasterVerificationGasLimit"
      let callGas ← if fault == .aboveCallCap then pure <| toJson ("0x1312d00" : String)
        else stable "callGasLimit"
      let postOpGas ← if fault == .zeroPaymasterGas then pure <| toJson ("0x0" : String)
        else stable "paymasterPostOpGasLimit"
      let mut fields := [
        ("verificationGasLimit", ← stable "verificationGasLimit"),
        ("callGasLimit", callGas),
        ("preVerificationGas", ← stable "preVerificationGas")]
      unless fault == .omitPaymasterGas || fault == .omitPaymasterVerification ||
          fault == .omitPaymasterGrowOnce do
        fields := fields ++ [("paymasterVerificationGasLimit",
          if fault == .zeroPaymasterGas then toJson ("0x0" : String)
          else if fault == .malformedPaymasterGas then
            toJson ("UNTRUSTED_PROVIDER_DETAIL_SENTINEL" : String)
          else paymasterGas)]
      unless fault == .omitPaymasterGas || fault == .omitPostOp ||
          fault == .omitPaymasterGrowOnce do
        fields := fields ++ [("paymasterPostOpGasLimit", postOpGas)]
      return .estimated (Json.mkObj fields)
    randomField := do
      if fault == .badRandom then return input.notes[0]!.nullifierHash
      random.modify (· + 1)
      random.get
    prove := fun request => do
      proofs.modify (· + 1)
      require ((← estimates.get) > 0) "Proof callback preceded estimation."
      return {
        requestHash := request.hash
        proof := ByteArray.empty
        signals := request.publicSignals }
    validateHistory := fun _ => histories.modify (· + 1) }
  try
    let quote ← if makeProof then do
      let prepared ← prepareWith effects input
      pure prepared.quote
      else estimateWith effects input
    return {
      quote := some quote
      estimates := ← estimates.get
      proofs := ← proofs.get
      histories := ← histories.get
      tokenQuotes := ← tokenQuotes.get
      error := false }
  catch error =>
    return {
      quote := none
      estimates := ← estimates.get
      proofs := ← proofs.get
      histories := ← histories.get
      tokenQuotes := ← tokenQuotes.get
      error := true, errorText := error.toString }

def main : IO UInt32 := do
  let input ← inputFor
  let batch ← inputFor false true
  let token ← inputFor true
  let baseline := baselineGas input false 3000000000 1000000000
  require (baseline.verification == 50000 && baseline.execution == 0 &&
    baseline.preVerification == 100000 && baseline.paymasterVerification == 450000 &&
    baseline.postOp == 50000 && SponsoredWithdrawal.ethFee baseline == 2340000000000000)
    "Direct alpha.38 gas baseline or 20% prefund buffer changed."
  let batchBaseline := baselineGas batch false 3000000000 1000000000
  require (batchBaseline.execution == 460000 && batchBaseline.verification == 50000)
    "Native batch baseline omitted direct withdrawals or forwarding gas."
  let undeployed := match batch.mode with
    | .batch account receiver calls => { batch with
        mode := .batch { account with deployed := false } receiver calls
        bounds := { batch.bounds with maxVerificationGas := 2000000 } }
    | _ => batch
  require ((baselineGas undeployed false 3000000000 1000000000).verification == 1000000 &&
    ({ } : Bundler.Bounds).maxVerificationGas == 1000000)
    "Undeployed account baseline or general bundler verification bound changed unexpectedly."
  let deployedEstimate ← scenario undeployed .undeployedVerificationEstimate
  require (!deployedEstimate.error && deployedEstimate.estimates == 2 &&
    deployedEstimate.proofs == 0 && deployedEstimate.quote.get!.gas.verification == 1450271)
    "A realistic account deployment estimate failed its bounded verification refinement."
  require ((baselineGas token true 1 1).paymasterVerification == 550000)
    "ERC20 sponsorship omitted the transfer-gas allowance."
  let normal ← scenario input
  require (!normal.error && normal.estimates == 1 && normal.proofs == 0 &&
    normal.quote.get!.estimation == .estimated && normal.quote.get!.requests[0]!.fee > 0 &&
    normal.quote.get!.requests[0]!.relayer == 0xb0ffcdc890e969579d348f519a9c3920c2dd04a5)
    "Stable direct estimation failed or generated proofs too early."
  require (normal.quote.get!.gas.maxFee == 3000000000)
    "Ordinary network base fees unexpectedly received tiny-base headroom."
  let tiny ← scenario input .tinyBase
  require (!tiny.error && tiny.quote.get!.gas.maxFee == 1156000019 &&
    tiny.quote.get!.gas.priority == 1155000000 &&
    tiny.quote.get!.fee == SponsoredWithdrawal.ethFee tiny.quote.get!.gas && tiny.proofs == 0)
    "Tiny-base headroom changed priority or failed to bind the initially padded fee."
  let capped ← scenario input .tinyBaseFullCap
  require (!capped.error && capped.quote.get!.gas.maxFee == 2000000042)
    "Tiny-base padding exceeded the unchanged host-reference price cap."
  let absoluteCap := { input.bounds with maxFeePerGas := 1155500019 }
  let clamped ← scenario { input with bounds := absoluteCap } .tinyBase
  require (!clamped.error && clamped.quote.get!.gas.maxFee == 1155500019)
    "Tiny-base padding exceeded the configured absolute max-fee cap."
  let invalidTiny ← scenario input .tinyBaseInvalidQuote
  require (invalidTiny.error && invalidTiny.estimates == 0 && invalidTiny.proofs == 0 &&
    invalidTiny.errorText.contains "Bundler gas prices exceed the local network-price or fee limits")
    "Tiny-base padding repaired an invalid original quote instead of rejecting it first."
  let threshold ← scenario input .thresholdBase
  require (!threshold.error && threshold.quote.get!.gas.maxFee == 3000000000)
    "Headroom applied at the excluded base-fee threshold."
  let growth ← scenario input .growOnce
  require (!growth.error && growth.estimates == 2 && growth.quote.get!.gas.verification == 60000)
    "Gas refinement did not buffer once and stabilize."
  for selected in [input, batch] do
    for fault in [Fault.omitPaymasterGas, .omitPaymasterVerification, .omitPostOp,
        .zeroPaymasterGas] do
      let omitted ← scenario selected fault
      require (!omitted.error && omitted.estimates == 1 && omitted.proofs == 0 &&
        omitted.quote.get!.gas.paymasterVerification == 450000 &&
        omitted.quote.get!.gas.postOp == 50000)
        "Omitted or zero optional paymaster fields inflated current floors instead of converging."
    let omittedGrowth ← scenario selected .omitPaymasterGrowOnce
    require (!omittedGrowth.error && omittedGrowth.estimates == 2 && omittedGrowth.proofs == 0 &&
      omittedGrowth.quote.get!.gas.paymasterVerification == 450000 &&
      omittedGrowth.quote.get!.gas.postOp == 50000)
      "Optional paymaster floors grew again during account verification refinement."
  let unavailable ← scenario input .unavailable
  require (!unavailable.error && unavailable.estimates == 2 &&
    unavailable.quote.get!.estimation == .fallback .transport &&
    unavailable.quote.get!.gas.verification == 150000 &&
    unavailable.quote.get!.gas.preVerification == 300000 &&
    unavailable.quote.get!.gas.paymasterVerification == 650000)
    "Known transport outage did not use the conservative direct fallback."
  let internal ← scenario input .internalUnavailable
  require (!internal.error && internal.estimates == 1 &&
    internal.quote.get!.estimation == .fallback .bundlerInternal)
    "Known internal estimation outage lost its explicit fallback classification."
  let required ← scenario { input with policy := .required } .unavailable
  require (required.error && required.proofs == 0) "Required estimation silently used fallback."
  let incompatible ← scenario input .validationOnlyEstimator
  require (!incompatible.error && incompatible.estimates == 1 && incompatible.proofs == 0 &&
    incompatible.quote.get!.estimation == .fallback .validationOnlyEstimator &&
    incompatible.quote.get!.gas.execution == 0 &&
    incompatible.quote.get!.gas.paymasterVerification == 650000 &&
    incompatible.quote.get!.requests[0]!.fee == incompatible.quote.get!.fee)
    "Validation-only fallback lost its bounds, zero execution gas or fee binding."
  let strictIncompatible ← scenario { input with policy := .required } .validationOnlyEstimator
  require (!strictIncompatible.error && strictIncompatible.estimates == 1 &&
    strictIncompatible.proofs == 0 &&
    strictIncompatible.quote.get!.estimation == .fallback .validationOnlyEstimator &&
    strictIncompatible.quote.get!.gas.execution == 0 &&
    strictIncompatible.quote.get!.fee == incompatible.quote.get!.fee &&
    strictIncompatible.quote.get!.requests == incompatible.quote.get!.requests)
    "Default required policy failed automatic known-incompatibility handling or changed fee binding."
  for policy in [Policy.required, .bestEffort] do
    let batchIncompatible ← scenario { batch with policy } .validationOnlyEstimator
    require (batchIncompatible.error && batchIncompatible.proofs == 0)
      "Batch execution gained the validation-only fallback."
  for fault in [Fault.unavailable, .internalUnavailable, .rejected] do
    let failed ← scenario { input with policy := .required } fault
    require (failed.error && failed.proofs == 0)
      "Automatic known-incompatibility handling bypassed another strict-mode failure."
  let gasBounds := { input.bounds with maxGasCostWei := 2500000000000000 }
  let overGas ← scenario { input with policy := .required, bounds := gasBounds } .validationOnlyEstimator
  require (overGas.error && overGas.estimates == 1 && overGas.proofs == 0)
    "Automatic fallback bypassed the maximum gas-cost bound."
  require (overGas.errorText == "Withdrawal gas: maximum gas cost 3450000000000000 wei exceeds limit 2500000000000000 wei.")
    "Gas-limit rejection lost its numeric field and configured bound."
  let overFee ← scenario { input with policy := .required, maxFeeBps := 3000 } .validationOnlyEstimator
  require (overFee.error && overFee.estimates == 1 && overFee.proofs == 0)
    "Automatic fallback bypassed the sponsoring-note fee bound."
  require (overFee.errorText == "The estimated gas fee exceeds the configured sponsoring-note fee limit.")
    "Fee-limit rejection lost its concise stage diagnostic."
  let badFallbackProof ← scenario { input with policy := .required } .validationOnlyEstimator true
  require (badFallbackProof.error && badFallbackProof.estimates == 1 &&
    badFallbackProof.histories == 2 && badFallbackProof.proofs == 1)
    "Automatic fallback skipped fresh history or accepted an invalid real proof."
  let batchFailure ← scenario batch .unavailable
  require (batchFailure.error && batchFailure.proofs == 0) "Batch preparation silently used fallback."
  let retry ← scenario { batch with executionGasRetry := true } .outOfGasOnce
  require (!retry.error && retry.estimates == 2 && retry.quote.get!.gas.execution == 920000)
    "Bounded execution-only out-of-gas retry failed to double its baseline."
  let some largePool := poolFor .mainnet "1" "ETH"
    | throw <| IO.userError "Missing large public fixture pool."
  let largePoolBytes ← checked <| parseHexBytes largePool.address
  let largeAddress := largePoolBytes.data.foldl (fun n b => n * 256 + b.toNat) 0
  let retryInput := { batch with
    executionGasRetry := true
    notes := batch.notes.map (fun note => { note with pool := largeAddress }) }
  let retryLimit ← scenario retryInput .outOfGasAlways
  require (retryLimit.error && retryLimit.estimates == 4 && retryLimit.proofs == 0)
    "Execution gas retries exceeded three bounded increases."
  let unstable ← scenario input .unstable
  require (unstable.error && unstable.estimates == 3 && unstable.proofs == 0)
    "Unstable gas estimates reached real proof creation."
  for fault in #[Fault.aboveGasCap, .rejected, .badRandom, .staleHead, .wrongChain,
      .emptyVerifier, .highPrice, .malformedEstimate, .malformedPaymasterGas] do
    let failed ← scenario input fault
    require (failed.error && failed.proofs == 0)
      "Rejected or malformed estimation data reached real proof creation."
  let overPaymaster ← scenario input .aboveGasCap
  require (overPaymaster.errorText == "Buffered withdrawal gas: paymasterVerificationGasLimit 2400000 exceeds limit 2000000 gas." &&
    overPaymaster.proofs == 0)
    "Buffered paymaster gas rejection did not identify the exact field and limit."
  let overCall ← scenario batch .aboveCallCap
  require (overCall.errorText == "Bundler gas estimate: callGasLimit 20000000 exceeds limit 8000000 gas." &&
    overCall.estimates == 1 && overCall.proofs == 0)
    "A bounded numeric bundler estimate was mislabeled as malformed or hid its exceeded field."
  let malformedOptional ← scenario input .malformedPaymasterGas
  require (malformedOptional.errorText == "The bundler returned a malformed gas estimate." &&
    !malformedOptional.errorText.contains "UNTRUSTED_PROVIDER_DETAIL_SENTINEL")
    "Malformed optional paymaster gas reflected provider text or lost its fixed diagnostic."
  let malformed ← scenario input .malformedEstimate
  require (malformed.errorText == "The bundler returned a malformed gas estimate." &&
    (malformed.errorText.splitOn "UNTRUSTED_PROVIDER_DETAIL_SENTINEL").length == 1)
    "Malformed estimate reflected provider data or hid its stage."
  let expensive ← scenario input .highPrice
  require (expensive.errorText == "Bundler gas prices exceed the local network-price or fee limits. Try again with a fresh quote or use another bundler.")
    "Fee-price rejection was reported as invalid public data."
  let repeated ← scenario { batch with notes := #[batch.notes[0]!, batch.notes[0]!] }
  require (repeated.error && repeated.estimates == 0 &&
    repeated.errorText == "Select distinct notes of the same asset and network.")
    "Duplicate selection reached estimation or lost its selection diagnostic."
  let historyFallback ← scenario input .malformedFeeHistory
  require (!historyFallback.error) "Bounded host fee-history fallback failed."
  let tokenQuote ← scenario token
  require (!tokenQuote.error && tokenQuote.tokenQuotes == 1 && tokenQuote.quote.get!.fee == 1000)
    "Token sponsorship omitted the paymaster quote or used ETH units as token units."
  for fault in #[Fault.zeroQuote, .consumingQuote] do
    let failed ← scenario token fault
    require (failed.error && failed.proofs == 0)
      "An invalid token quote reached proof creation."
  let zeroFee ← scenario token .zeroQuote
  require (zeroFee.errorText == "The paymaster returned a zero fee quote; withdrawal preparation stopped.")
    "A zero token fee quote lost its diagnostic."
  let consumingFee ← scenario token .consumingQuote
  require (consumingFee.errorText == "The estimated gas fee exceeds the first note's amount. Use a larger first note or fewer withdrawals.")
    "A fee consuming the sponsor note was reported as generic invalid public data."
  let proofBoundary ← scenario input .none true
  require (proofBoundary.error && proofBoundary.estimates == 1 &&
    proofBoundary.histories == 2 && proofBoundary.proofs == 1)
    "Proof output bypassed verification or was requested before final estimate/revalidation."
  require (proofBoundary.errorText == "The generated withdrawal proof failed local verification; nothing was submitted.")
    "Invalid real proof lost its local-verification diagnostic."
  IO.println "PASS: dummy-only paymaster estimates, bounded refinement and fallback, fee quotes, and final proof boundary"
  return 0
