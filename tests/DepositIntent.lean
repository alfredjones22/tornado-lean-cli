import Tornado.Cli.DepositMulti

/-! Offline tests using original public catalog inputs, actual public planners,
independent calldata mutations and synthetic typed transaction signatures. -/

open Tornado.Domain Tornado.Protocol Tornado.Crypto
open Tornado.Cli

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def address (text : String) : IO Nat := do
  let bytes ← checked <| parseHexBytes text
  return bytes.data.foldl (fun n b => n * 256 + b.toNat) 0

private def commit (n : Nat) : ByteArray :=
  (Abi.uintWord n).toOption.getD ByteArray.empty

private def rejecting (input : DepositIntent.Input) (plan : DepositIntent.EncodedPlan) : IO Unit :=
  require (!(DepositIntent.accept input plan).isOk) "An unreviewed deposit mutation was accepted."

def main : IO UInt32 := do
  let some ethA := poolFor .mainnet "0.01" "ETH" | throw <| IO.userError "Missing ETH pool."
  let some ethB := poolFor .mainnet "0.1" "ETH" | throw <| IO.userError "Missing ETH pool."
  let items : Array DepositMulti.Item := #[⟨ethA, commit 1⟩, ⟨ethB, commit 2⟩]
  let readings : DepositMulti.Readings := {
    chainId := 1, senderCode := ByteArray.empty, ethBalance := 10 ^ 20,
    pools := #[⟨← address ethA.address, ethA.amount, 0⟩, ⟨← address ethB.address, ethB.amount, 0⟩] }
  let prepared ← checked <| DepositMulti.preparePlan items .mainnet 123 readings false
  let plan := DepositMulti.planEncoding prepared.output
  require (plan.mode == .simple7702 && plan.batches.size == 1 &&
    prepared.checked.meaning.batches[0]![0]!.value == ethA.amount &&
    prepared.checked.meaning.batches[0]![1]!.value == ethB.amount)
    "The actual planner lost denomination-valued deposit order."
  let exactPrincipal := ethA.amount + ethB.amount
  let creditPrepared ← checked <| DepositMulti.preparePlan items .mainnet 123
    { readings with ethBalance := exactPrincipal } false false 1
  require (creditPrepared.input.ethBalance == exactPrincipal &&
    creditPrepared.input.entryPointGasCredit == 1)
    "Certified deposit input replaced a real wallet balance with EntryPoint credit."
  rejecting { creditPrepared.input with entryPointGasCredit := 0 }
    (DepositMulti.planEncoding creditPrepared.output)
  rejecting { creditPrepared.input with ethBalance := exactPrincipal - 1, entryPointGasCredit := 10 ^ 20 }
    (DepositMulti.planEncoding creditPrepared.output)
  let steps := plan.batches[0]!
  for changed in #[
    { steps[0]! with to := 8 }, { steps[0]! with value := ethA.amount + 1 },
    { steps[0]! with pool := 8 }, { steps[0]! with spender := 8 },
    { steps[0]! with approvalAmount := 1 },
    { steps[0]! with commitment := commit 8 },
    { steps[0]! with data := steps[0]!.data.push 0 },
    { steps[0]! with data := ← checked <| Abi.poolDeposit (commit 8), commitment := commit 8 }] do
    rejecting prepared.input { plan with batches := #[steps.set! 0 changed] }
  rejecting prepared.input { plan with batches := #[#[steps[1]!, steps[0]!]] }
  rejecting prepared.input { plan with batches := #[#[steps[0]!]] }
  rejecting prepared.input { plan with batches := #[steps.push steps[0]!] }
  rejecting prepared.input { plan with batches := #[] }
  rejecting prepared.input { plan with noteCount := 1 }
  rejecting prepared.input { plan with amount := plan.amount + 1 }
  rejecting prepared.input { plan with mode := .sequential }
  rejecting prepared.input { plan with reason := .forcedSequential }
  let forced ← checked <| DepositMulti.preparePlan items .mainnet 123 readings true
  require (forced.output.mode == .sequential && forced.output.reason == .forcedSequential)
    "Forced sequential intent was changed."
  let contract ← checked <| DepositMulti.preparePlan items .mainnet 123
    { readings with senderCode := ByteArray.mk #[0xef] } false
  require (contract.output.reason == .contractOrDelegated) "Sender code route reason changed."
  let single ← checked <| DepositMulti.preparePlan #[items[0]!] .mainnet 123 readings false
  require (single.output.reason == .singleDeposit) "Single ETH deposit route reason changed."
  let some tokenPool := poolFor .mainnet "100" "USDC" | throw <| IO.userError "Missing token pool."
  let tokenItems : Array DepositMulti.Item := (List.range 6).toArray.map
    (fun i => ⟨tokenPool, commit (100 + i)⟩)
  let tokenReadings : DepositMulti.Readings := {
    chainId := 1, senderCode := ByteArray.empty, ethBalance := 10 ^ 20,
    tokenBalance := 6 * tokenPool.amount,
    pools := #[⟨← address tokenPool.address, tokenPool.amount, 1⟩] }
  let token ← checked <| DepositMulti.preparePlan tokenItems .mainnet 123 tokenReadings false
  let tokenPlan := DepositMulti.planEncoding token.output
  let tokenSteps := tokenPlan.batches[0]!
  require (tokenPlan.batches.size == 2 && tokenSteps.size == 6 &&
    tokenSteps[0]!.kind == .reset && tokenSteps[1]!.kind == .approve &&
    tokenSteps[1]!.approvalAmount == 4 * tokenPool.amount &&
    tokenPlan.batches[1]!.size == 2 && tokenPlan.batches[1]!.all (fun s => s.kind == .deposit))
    "First chunk approval amount or deposit-only future chunk changed."
  let mutateApproval (index : Nat) (spender amount : Nat) : IO Unit := do
    let data ← checked <| Abi.erc20Approve spender amount
    let changed := { tokenSteps[index]! with data, spender, approvalAmount := amount }
    rejecting token.input { tokenPlan with batches := tokenPlan.batches.set! 0 (tokenSteps.set! index changed) }
  mutateApproval 0 tokenSteps[0]!.spender 1
  mutateApproval 1 tokenSteps[1]!.spender (6 * tokenPool.amount)
  mutateApproval 1 8 (4 * tokenPool.amount)
  for changed in #[
    { tokenSteps[1]! with value := 1 }, { tokenSteps[1]! with to := 8 },
    { tokenSteps[1]! with data := tokenSteps[1]!.data.push 0 },
    { tokenSteps[1]! with approvalAmount := 1 },
    { tokenSteps[2]! with value := tokenPool.amount }] do
    let index := if changed.kind == .deposit then 2 else 1
    rejecting token.input { tokenPlan with batches := tokenPlan.batches.set! 0 (tokenSteps.set! index changed) }
  rejecting token.input { tokenPlan with batches := tokenPlan.batches.set! 0 (tokenSteps.extract 1 tokenSteps.size) }
  let later := tokenItems.extract 4 6
  let fresh ← checked <| DepositMulti.preparePlan later .mainnet 123
    { tokenReadings with pools := #[⟨← address tokenPool.address, tokenPool.amount, 0⟩] } true
  require (fresh.output.batches[0]!.size == 3 &&
    fresh.output.batches[0]![0]!.approvalAmount == 2 * tokenPool.amount)
    "Fresh later-phase plan reused the original allowance or approval amount."
  let enough ← checked <| DepositMulti.preparePlan later .mainnet 123
    { tokenReadings with pools := #[⟨← address tokenPool.address, tokenPool.amount, 2 * tokenPool.amount⟩] } true
  require (enough.output.batches[0]!.size == 2) "Sufficient fresh allowance caused an extra approval."
  let thirteen : Array DepositMulti.Item := (List.range 13).toArray.map (fun i => ⟨ethA, commit (200 + i)⟩)
  let chunked ← checked <| DepositMulti.preparePlan thirteen .mainnet 123 readings false
  require (chunked.output.batches.size == 2 && chunked.output.batches[0]!.size == 11 &&
    chunked.output.batches[1]!.size == 2) "ETH singleton-tail avoidance changed."
  let invoiceText ← checked <| invoiceForNote ethA ("0x" ++ bytesToHex (commit 42))
  let invoice ← checked <| parseInvoice invoiceText .mainnet
  let invoicePlan ← checked <| DepositSend.prepareInvoice invoice 123 ⟨1, ethA.amount, 10 ^ 20, 0, 0⟩
  require (invoicePlan.steps.size == 1) "Public invoice route required a note secret."
  let step := invoicePlan.steps[0]!
  let tx : Rlp.Transaction1559 := {
    chainId := 1, nonce := 3, maxPriorityFeePerGas := 1, maxFeePerGas := 2,
    gas := 100000, to := some step.to, value := step.value, data := step.data }
  let signature : Rlp.Signature := { yParity := 0, r := 1, s := 1 }
  let raw ← checked <| Rlp.serialize1559 tx (some signature)
  let signed : TypedTransaction.SignedTyped := {
    signingHash := ← checked <| Rlp.signingHash1559 tx, signature, serialized := raw,
    transactionHash := keccak256 raw }
  let _ ← checked <| DepositSend.certifySignedStep step tx signed
  require (!(DepositIntent.acceptSignedStep (DepositSend.stepEncoding step)
    { tx with value := tx.value + 1 } raw).isOk) "Signed transaction value mutation was accepted."
  require (!(DepositIntent.acceptSignedStep (DepositSend.stepEncoding step)
    { tx with nonce := tx.nonce + 1 } raw).isOk) "Signed transaction nonce mutation was accepted."
  require (!(DepositIntent.acceptSignedStep (DepositSend.stepEncoding step) tx (raw.push 0)).isOk)
    "Signed transaction trailing bytes were accepted."
  require (!(DepositIntent.acceptSignedStep (DepositSend.stepEncoding step) tx
    (← checked <| Rlp.serialize1559 tx none)).isOk) "Unsigned deposit transaction was accepted."
  IO.println "PASS: actual deposit planner intent, ordered funding, reset/exact approval, chunk/reason limits, fresh phase replanning, public invoices, signed-step decoding and mutations"
  return 0
