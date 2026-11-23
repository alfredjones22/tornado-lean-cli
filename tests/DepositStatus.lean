import Lean
import Tornado.Cli.DepositStatus

open Lean Tornado.Cli.DepositStatus Tornado.Domain Tornado.Protocol

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def replace (json : Json) (name : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert name value)
  | other => other

private def changeStep (json : Json) (name : String) (value : Json) : Except String Json := do
  let steps ← (← json.getObjVal? "steps").getArr?
  let first := replace steps[0]! name value
  return replace json "steps" (toJson (steps.set! 0 first))

private def check (raw : String) : Except String Unit := do
  let journal ← parseJournal raw
  require (journal.chainId == .mainnet && journal.steps.size == 1)
    "Pinned TypeScript journal shape changed."
  let step := journal.steps[0]!
  require (step.kind == .deposit && step.status == .prepared &&
    step.hash == some ("0x" ++ String.intercalate "" (List.replicate 32 "97")))
    "The synthetic transaction hash changed."
  let some deposit := step.expectedDeposit
    | throw "Deposit expectation was not parsed."
  require (deposit.pool == step.to && deposit.commitment.size == 32)
    "Pinned catalog pool or commitment changed."
  let some hashText := step.hash | throw "Prepared step lost its hash."
  let transactionHash ← parseHexBytes hashText
  let blockHash ← parseHexBytes ("0x" ++ String.ofList (List.replicate 64 '7'))
  let log : Events.Log :=
    ⟨deposit.pool, #[Events.depositTopic, deposit.commitment],
      ⟨Array.replicate 64 0⟩⟩
  let receipt : RpcReceipt.Receipt := {
    transactionHash, blockHash, blockNumber := 1, transactionIndex := 0,
    origin := journal.account, to := some step.to, success := true,
    logs := [log] }
  require (classify journal step (some receipt) == .confirmed)
    "Exact pool Deposit event did not confirm."
  require (classify journal step none == .unknown)
    "Missing chain receipt did not remain unknown."
  require (classify journal step (some { receipt with logs := [] }) == .unknown)
    "Receipt without Deposit event was accepted."
  require (classify journal step (some { receipt with origin := 1 }) == .unknown)
    "Receipt from a different sender was accepted."
  require (classify journal step (some { receipt with transactionHash := blockHash }) == .unknown)
    "Receipt for a different transaction was accepted."
  require (classify journal step (some { receipt with to := some 1 }) == .unknown)
    "Receipt to a different contract was accepted."
  require (classify journal step (some { receipt with success := false }) == .reverted)
    "Exact reverted receipt was not classified as reverted."
  let output ← render journal #[.confirmed]
  require (output == s!"1. confirmed\tDeposit 0.01 ETH\t{hashText}\n" ++
    "Read-only inspection; journal statuses were not updated.\n")
    "Read-only output or warning changed."
  require (!(render journal #[]).isOk) "Mismatched status array was rendered."

  let json ← Json.parse raw
  require (!(parseJournal (replace json "kind" (toJson "deposit-7702-batch")).compress).isOk)
    "Batched journal was accepted as sequential."
  require (!(parseJournal ((← changeStep json "pool" (toJson
    "0x1111111111111111111111111111111111111111")).compress)).isOk)
    "Unpinned pool was accepted."
  require (!(parseJournal ((← changeStep json "commitment" (toJson "0x1234")).compress)).isOk)
    "Malformed commitment was accepted."
  require (!(parseJournal ((← changeStep json "hash" (toJson "0x1234")).compress)).isOk)
    "Malformed transaction hash was accepted."
  require (!(parseJournal ((← changeStep json "label" (toJson "bad\nlabel")).compress)).isOk)
    "Multiline journal label was accepted."
  require (!(parseJournal ((← changeStep json "status" (toJson "confirmed-no-hash")).compress)).isOk)
    "Unknown journal status was accepted."
  return ()

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/deposit-status-journal.json"
  match check raw with
  | .error message =>
      IO.eprintln message
      return 1
  | .ok () =>
      let help ← inspectCommand ["--help"]
      if !help.startsWith "Usage: tornado deposit inspect-status" then
        IO.eprintln "Inspect-status help changed."
        return 1
      IO.println "PASS: pinned sequential journal, exact receipt classification, and read-only rendering"
      return 0
