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
  | none | growOnce | unstable | aboveGasCap | rejected | unavailable
  | internalUnavailable | outOfGasOnce | outOfGasAlways | badRandom
  | staleHead | wrongChain | emptyVerifier | highPrice | zeroQuote | consumingQuote
  | malformedFeeHistory | malformedEstimate
  deriving BEq

private structure Run where
  quote : Option Quote
  estimates : Nat
  proofs : Nat
  histories : Nat
  tokenQuotes : Nat
  error : Bool

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
        return Json.mkObj [
          ("baseFeePerGas", toJson #["0x3b9aca00", "0x3b9aca00"]),
          ("reward", toJson #[#["0x3b9aca00"]])]
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
      return Json.mkObj [("standard", Json.mkObj [
        ("maxFeePerGas", toJson (if fault == .highPrice then "0xe8d4a51000" else "0xb2d05e00")),
        ("maxPriorityFeePerGas", toJson ("0x3b9aca00" : String))])]
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
      if fault == .outOfGasAlways || (fault == .outOfGasOnce && (← estimates.get) == 1) then
        return .executionOutOfGas
      if fault == .malformedEstimate then return .estimated (Json.mkObj [])
      let stable (name : String) : IO Json := do
        let current ← qty (← field operation name)
        let value := if fault == .unstable ||
            (fault == .growOnce && (← estimates.get) == 1 && name == "verificationGasLimit") then current
          else current * 10 / 12
        return toJson (Bundler.quantity value)
      let paymasterGas ← if fault == .aboveGasCap then pure <| toJson ("0x1e8480" : String)
        else stable "paymasterVerificationGasLimit"
      return .estimated (Json.mkObj [
        ("verificationGasLimit", ← stable "verificationGasLimit"),
        ("callGasLimit", ← stable "callGasLimit"),
        ("preVerificationGas", ← stable "preVerificationGas"),
        ("paymasterVerificationGasLimit", paymasterGas),
        ("paymasterPostOpGasLimit", ← stable "paymasterPostOpGasLimit")])
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
  catch _ =>
    return {
      quote := none
      estimates := ← estimates.get
      proofs := ← proofs.get
      histories := ← histories.get
      tokenQuotes := ← tokenQuotes.get
      error := true }

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
  require (batchBaseline.execution == 460000)
    "Native batch baseline omitted direct withdrawals or forwarding gas."
  require ((baselineGas token true 1 1).paymasterVerification == 550000)
    "ERC20 sponsorship omitted the transfer-gas allowance."
  let normal ← scenario input
  require (!normal.error && normal.estimates == 1 && normal.proofs == 0 &&
    normal.quote.get!.estimation == .estimated && normal.quote.get!.requests[0]!.fee > 0 &&
    normal.quote.get!.requests[0]!.relayer == 0xb0ffcdc890e969579d348f519a9c3920c2dd04a5)
    "Stable direct estimation failed or generated proofs too early."
  let growth ← scenario input .growOnce
  require (!growth.error && growth.estimates == 2 && growth.quote.get!.gas.verification == 60000)
    "Gas refinement did not buffer once and stabilize."
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
      .emptyVerifier, .highPrice, .malformedEstimate] do
    let failed ← scenario input fault
    require (failed.error && failed.proofs == 0)
      "Rejected or malformed estimation data reached real proof creation."
  let historyFallback ← scenario input .malformedFeeHistory
  require (!historyFallback.error) "Bounded host fee-history fallback failed."
  let tokenQuote ← scenario token
  require (!tokenQuote.error && tokenQuote.tokenQuotes == 1 && tokenQuote.quote.get!.fee == 1000)
    "Token sponsorship omitted the paymaster quote or used ETH units as token units."
  for fault in #[Fault.zeroQuote, .consumingQuote] do
    let failed ← scenario token fault
    require (failed.error && failed.proofs == 0)
      "An invalid token quote reached proof creation."
  let proofBoundary ← scenario input .none true
  require (proofBoundary.error && proofBoundary.estimates == 1 &&
    proofBoundary.histories == 2 && proofBoundary.proofs == 1)
    "Proof output bypassed verification or was requested before final estimate/revalidation."
  IO.println "PASS: dummy-only paymaster estimates, bounded refinement and fallback, fee quotes, and final proof boundary"
  return 0
