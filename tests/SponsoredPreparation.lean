import Tornado.Cli.SponsoredWithdraw

/-! Exercise the production post-proving refresh/clock seam with an injected
slow prover. No proof, private note, key, RPC or transaction is used. -/

open Lean Tornado.Cli

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def gasFields (gas : Tornado.Protocol.SponsoredWithdrawal.Gas) : Array Nat :=
  #[gas.verification, gas.execution, gas.preVerification, gas.paymasterVerification,
    gas.postOp, gas.maxFee, gas.priority]

def main : IO UInt32 := do
  let parsed ← match SponsoredWithdraw.parseOptions
      ["--rpc=https://rpc.example.org/?a=b=c", "--broadcast"] {} with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  require (parsed.rpc == some "https://rpc.example.org/?a=b=c" && parsed.experimental)
    "An equals-style RPC option lost part of its query string."
  require (!(SponsoredWithdraw.parseOptions ["--simulation-policy", "ignore-failures"] {}).isOk)
    "Unknown simulation policy was accepted."
  let unattended ← match SponsoredWithdraw.parseOptions
      ["--broadcast", "--non-interactive", "--recipient", "0x1111111111111111111111111111111111111111"] {} with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  require (unattended.experimental && unattended.nonInteractive && !unattended.yes)
    "Explicit non-interactive authorization was conflated with --yes."
  let yesFailure ← try
    let _ ← SponsoredWithdraw.command false ["--broadcast", "--non-interactive", "--yes"]
    pure ""
  catch error => pure error.toString
  require (yesFailure == "Withdrawals require typed WITHDRAW approval; --yes is unavailable.")
    "--non-interactive silently accepted the unsupported --yes flag."
  let noOwner ← try
    let _ ← SponsoredWithdraw.command true ["--broadcast", "--non-interactive"]
    pure ""
  catch error => pure error.toString
  require (noOwner == "--non-interactive requires --owner-key-file for batch withdrawals.")
    "Unattended batch mode reached an owner-key prompt or network without a key file."
  let relayerYes ← try
    let _ ← RelayerWithdraw.run {
      noteFile := "/public-fixture", recipient := "0x1111111111111111111111111111111111111111",
      workerPath := "/public-worker-fixture", provingRoot := "/public-assets-fixture",
      rpcUrl := "https://rpc.example.test", experimental := true, nonInteractive := true, yes := true }
    pure ""
  catch error => pure error.toString
  require (relayerYes == "Relayer withdrawals require typed WITHDRAW approval; --yes is unavailable.")
    "Non-interactive relayer mode bypassed an invalid CLI admission rule."
  let events ← IO.mkRef (#[] : Array String)
  let clock ← IO.mkRef (1000 : Nat)
  let proofCalls ← IO.mkRef (0 : Nat)
  let oldGas : Tornado.Protocol.SponsoredWithdrawal.Gas := {
    execution := 100000, maxFee := 3001000026, priority := 3000000000 }
  let lowerGas := { oldGas with maxFee := 2001000026, priority := 2000000000 }
  let request : Tornado.Protocol.ProverWorkerWire.Request := {
    (default : Tornado.Protocol.ProverWorkerWire.Request) with
    chainId := 1, pool := 1, commitment := 2, nullifierHash := 3, root := 4,
    recipient := 5, relayer := 6, fee := 123 }
  let note : Tornado.Protocol.SponsoredWithdrawal.NoteProof := {
    request, result := { requestHash := ⟨#[1,2]⟩, proof := ⟨#[3,4]⟩, signals := request.publicSignals } }
  let prepared : PaymasterPrepare.Prepared := {
    quote := { (default : PaymasterPrepare.Quote) with
      input := { (default : PaymasterPrepare.Input) with notes := #[request], bounds := {} },
      gas := oldGas, fee := 123, requests := #[request], estimation := .estimated }, notes := #[note] }
  let (result, reviewedGas, reviewedAt) ← SponsoredWithdraw.finishPreparationWith
    (do
      proofCalls.modify (· + 1)
      events.modify (·.push "prove")
      -- More than the final review's five-minute TTL elapses while proving.
      clock.set 601001
      events.modify (·.push "proofs-complete")
      return prepared)
    (fun candidate => do
      require (candidate.quote.fee == 123) "Preparation changed the proof-bound fee."
      events.modify (·.push "refresh-history-gas-account")
      clock.set 601100
      return lowerGas)
    (do
      events.modify (·.push "review-clock")
      clock.get)
  require (result.quote.fee == 123 && result.quote.requests == prepared.quote.requests &&
    result.quote.input.notes == prepared.quote.input.notes && result.quote.estimation == prepared.quote.estimation &&
    gasFields result.quote.gas == gasFields oldGas &&
    result.notes.map (·.request) == prepared.notes.map (·.request) &&
    result.notes.map (·.result) == prepared.notes.map (·.result) &&
    gasFields reviewedGas == gasFields lowerGas && (← proofCalls.get) == 1 && reviewedAt == 601100 &&
    (← events.get) == #["prove", "proofs-complete", "refresh-history-gas-account", "review-clock"])
    "Bid refresh changed preparation/proofs, reproved, lost the lowered review bid or consumed the fresh review window."
  let finalClockReads ← IO.mkRef (0 : Nat)
  let reachedReview ← IO.mkRef false
  let rejected ← try
    let _ ← SponsoredWithdraw.finishPreparationWith (pure prepared)
      (fun _ => throw <| IO.userError "Injected stale price or spent root")
      (do finalClockReads.modify (· + 1); pure 0)
    reachedReview.set true
    pure false
    catch _ => pure true
  require (rejected && !(← reachedReview.get) && (← finalClockReads.get) == 0)
    "A failed post-proof refresh reached the final review clock."
  for invalid in #[
      { lowerGas with verification := oldGas.verification + 1 },
      { lowerGas with execution := oldGas.execution + 1 },
      { lowerGas with preVerification := oldGas.preVerification + 1 },
      { lowerGas with paymasterVerification := oldGas.paymasterVerification + 1 },
      { lowerGas with postOp := oldGas.postOp + 1 },
      { lowerGas with verification := oldGas.verification - 1 },
      { lowerGas with execution := oldGas.execution - 1 },
      { lowerGas with preVerification := oldGas.preVerification - 1 },
      { lowerGas with paymasterVerification := oldGas.paymasterVerification - 1 },
      { lowerGas with postOp := oldGas.postOp - 1 },
      { lowerGas with maxFee := oldGas.maxFee + 1 },
      { lowerGas with priority := oldGas.priority + 1 },
      { lowerGas with maxFee := 0 }] do
    let invalidRejected ← try
      let _ ← SponsoredWithdraw.finishPreparationWith (pure prepared) (fun _ => pure invalid)
        (do finalClockReads.modify (· + 1); pure 0)
      pure false
    catch _ => pure true
    require (invalidRejected && (← finalClockReads.get) == 0)
      "Changed gas limits, an upward bid or invalid prices reached the final review clock."
  let refreshCalls ← IO.mkRef (0 : Nat)
  let provingRejected ← try
    let _ ← SponsoredWithdraw.finishPreparationWith
      (throw <| IO.userError "Injected prover failure")
      (fun _ => do refreshCalls.modify (· + 1); pure oldGas)
      (do finalClockReads.modify (· + 1); pure 0)
    pure false
    catch _ => pure true
  require (provingRejected && (← refreshCalls.get) == 0 && (← finalClockReads.get) == 0)
    "A failed prover reached public refresh or final review."
  IO.println "PASS: slow proving precedes fresh history, gas and account checks and a new review clock; failures stop before review"
  return 0
