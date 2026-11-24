import Tornado.Cli.DepositBatch7702

open Tornado.Cli Tornado.Domain Tornado.Protocol

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def call (step : DepositSend.Step) : Abi.ContractCall :=
  ⟨step.to, step.value, step.data⟩

private def rejected (steps : Array DepositSend.Step) (bytes : ByteArray) : IO Unit :=
  require (!(DepositCallsIntent.accept (steps.map DepositSend.stepEncoding) bytes).isOk)
    "An unreviewed deposit account execution was accepted."

def main : IO UInt32 := do
  let some pool := poolFor .mainnet "0.01" "ETH"
    | throw <| IO.userError "Missing pinned pool."
  let commitment ← checked <| Abi.uintWord 42
  let invoice ← checked <| invoiceForNote pool ("0x" ++ Tornado.Crypto.bytesToHex commitment)
  let publicInvoice ← checked <| parseInvoice invoice .mainnet
  let steps ← checked <| DepositSend.planInvoice publicInvoice 123 ⟨1, pool.amount, 10 ^ 20, 0, 0⟩
  let step := steps[0]!
  let otherCommitment ← checked <| Abi.uintWord 43
  let otherData ← checked <| Abi.poolDeposit otherCommitment
  let single ← checked <| DepositBatch7702.callsData steps
  let _ ← checked <| DepositCallsIntent.accept (steps.map DepositSend.stepEncoding) single
  require ((← checked <| DepositCallsIntent.decode single).size == 1)
    "Single execution did not decode one deposit."
  for changed in #[{ step with to := step.to + 1 }, { step with value := step.value + 1 },
      { step with data := otherData }] do
    rejected steps (← checked <| Abi.accountExecute changed.to changed.value changed.data)
  rejected steps (single.push 0)
  rejected steps (single.set! 0 0)
  rejected #[] single
  let paired := #[step, { step with commitment := otherCommitment, data := otherData }]
  let batch ← checked <| DepositBatch7702.callsData paired
  let certificate ← checked <| DepositCallsIntent.accept (paired.map DepositSend.stepEncoding) batch
  require (certificate.calls.size == 2) "Batch execution lost a selected deposit."
  rejected paired (← checked <| Abi.accountExecuteBatchComposed #[call paired[1]!, call paired[0]!])
  rejected paired single
  rejected steps batch
  rejected paired (batch.push 0)
  let token : Nat := 99
  let spender := step.to
  let resetData ← checked <| Abi.erc20Approve spender 0
  let approveData ← checked <| Abi.erc20Approve spender pool.amount
  let reset : DepositSend.Step := {
    kind := .reset, label := "reset", to := token, value := 0,
    data := resetData, spender, approvalAmount := 0 }
  let approve : DepositSend.Step := {
    kind := .approve, label := "approve", to := token, value := 0,
    data := approveData,
    spender, approvalAmount := pool.amount }
  let tokenSteps := #[reset, approve, { step with value := 0 }]
  let tokenData ← checked <| DepositBatch7702.callsData tokenSteps
  let _ ← checked <| DepositCallsIntent.accept (tokenSteps.map DepositSend.stepEncoding) tokenData
  for changed in #[{ approve with to := token + 1 }, { approve with value := 1 },
      { approve with data := ← checked <| Abi.erc20Approve (spender + 1) pool.amount },
      { approve with data := ← checked <| Abi.erc20Approve spender (pool.amount + 1) }] do
    rejected tokenSteps (← checked <| Abi.accountExecuteBatchComposed
      #[call reset, call changed, call tokenSteps[2]!])
  rejected tokenSteps (← checked <| Abi.accountExecuteBatchComposed
    #[call approve, call tokenSteps[2]!])
  let operation : UserOperation08.UserOperation := { sender := 123, callData := tokenData }
  let _ ← checked <| DepositCallsIntent.acceptOperation
    (tokenSteps.map DepositSend.stepEncoding) operation
  require (!(DepositCallsIntent.acceptOperation (tokenSteps.map DepositSend.stepEncoding)
    { operation with callData := batch }).isOk) "Final operation bypassed deposit intent."
  IO.println "PASS: actual Simple7702 deposit call decoding, ordered commitments, reset/exact approval, final-operation binding and mutation rejection"
  return 0
