import Tornado.Cli.SponsoredWithdraw

/-! Exercise the production post-proving refresh/clock seam with an injected
slow prover. No proof, private note, key, RPC or transaction is used. -/

open Lean Tornado.Cli

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

def main : IO UInt32 := do
  let parsed ← match SponsoredWithdraw.parseOptions
      ["--rpc=https://rpc.example.org/?a=b=c", "--experimental-send"] {} with
    | .ok value => pure value
    | .error message => throw <| IO.userError message
  require (parsed.rpc == some "https://rpc.example.org/?a=b=c" && parsed.experimental)
    "An equals-style RPC option lost part of its query string."
  require (!(SponsoredWithdraw.parseOptions ["--simulation-policy", "ignore-failures"] {}).isOk)
    "Unknown simulation policy was accepted."
  let events ← IO.mkRef (#[] : Array String)
  let clock ← IO.mkRef (1000 : Nat)
  let prepared : PaymasterPrepare.Prepared := {
    quote := { (default : PaymasterPrepare.Quote) with fee := 123 }, notes := #[] }
  let (result, reviewedAt) ← SponsoredWithdraw.finishPreparationWith
    (do
      events.modify (·.push "prove")
      -- More than the final review's five-minute TTL elapses while proving.
      clock.set 601001
      events.modify (·.push "proofs-complete")
      return prepared)
    (fun candidate => do
      require (candidate.quote.fee == 123) "Preparation changed the proof-bound fee."
      events.modify (·.push "refresh-history-gas-account")
      clock.set 601100)
    (do
      events.modify (·.push "review-clock")
      clock.get)
  require (result.quote.fee == 123 && reviewedAt == 601100 &&
    (← events.get) == #["prove", "proofs-complete", "refresh-history-gas-account", "review-clock"])
    "Slow proving consumed the fresh review window or skipped final public revalidation."
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
  let refreshCalls ← IO.mkRef (0 : Nat)
  let provingRejected ← try
    let _ ← SponsoredWithdraw.finishPreparationWith
      (throw <| IO.userError "Injected prover failure")
      (fun _ => refreshCalls.modify (· + 1))
      (do finalClockReads.modify (· + 1); pure 0)
    pure false
    catch _ => pure true
  require (provingRejected && (← refreshCalls.get) == 0 && (← finalClockReads.get) == 0)
    "A failed prover reached public refresh or final review."
  IO.println "PASS: slow proving precedes fresh history, gas and account checks and a new review clock; failures stop before review"
  return 0
