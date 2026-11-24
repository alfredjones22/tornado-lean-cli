import Tornado.Protocol.SponsoredWithdrawal

/-! Synthetic public-byte mutation checks of the independent semantic gate.
These fixtures exercise ABI and accounting requirements, not proof validity. -/

open Tornado.Protocol Tornado.Protocol.UserOperation08
open Tornado.Protocol.BatchWithdrawalIntent

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def note (pool root nullifier : Nat) (amount : Nat) (sponsor : Bool := false) : Note := {
  withdrawal := {
    pool, proof := Array.replicate 256 11, root, nullifierHash := nullifier,
    recipient := 1, relayer := if sponsor then 4 else 0,
    fee := if sponsor then 7 else 0, refund := 0 },
  denomination := amount }

private def intent : Intent := {
  notes := #[note 3 13 17 1000 true, note 5 19 23 2000, note 6 29 31 3000],
  account := 1, owner := 9, nonce := 5, deployed := true, receiver := 1,
  sponsor := 4, token := none,
  tail := #[{ to := 10, value := 3, data := ByteArray.mk #[0x12, 0x34] },
    { to := 11, value := 0, data := ByteArray.mk #[0x56] }],
  verificationGas := 50000, executionGas := 500000,
  preVerificationGas := 100000, paymasterVerificationGas := 450000,
  postOpGas := 50000, maxFee := 1000000000, priorityFee := 100000000 }

private def withdrawalCall (w : Withdrawal) : IO Abi.ContractCall := do
  let data ← checked <| Abi.poolWithdraw
    (ByteArray.mk w.proof) (← checked <| Abi.uintWord w.root)
    (← checked <| Abi.uintWord w.nullifierHash) w.recipient w.relayer w.fee w.refund
  return { to := w.pool, value := 0, data }

/-- Honest encoders provide fixture bytes; only independent decoding and
field comparison decide whether the production gate accepts them. -/
private def operation (input : Intent) : IO UserOperation := do
  let first := input.notes[0]!.withdrawal
  let mut calls ← (input.notes.extract 1 input.notes.size).mapM fun n => withdrawalCall n.withdrawal
  calls := calls ++ input.tail
  if input.tail.isEmpty && input.receiver != input.account then
    let call : Abi.ContractCall ← match input.token with
      | none => pure { to := input.receiver, value := net input, data := ByteArray.empty }
      | some token => do
        let data ← checked <| Abi.erc20Transfer input.receiver (net input)
        pure { to := token, value := 0, data }
    calls := calls.push call
  let factoryData ← if input.deployed then pure ByteArray.empty
    else checked <| Tornado.SmartAccount.accountFactoryData input.owner
  return {
    sender := input.account, nonce := input.nonce,
    factory := if input.deployed then none
      else some (.address 0x13e9ed32155810fdbd067d4522c492d6f68e5944),
    factoryData,
    callData := ← checked <| Abi.accountExecuteBatchComposed calls,
    paymaster := some input.sponsor,
    paymasterData := ← checked <| Abi.sponsorParameters {
      instanceAddress := first.pool, proof := ByteArray.mk first.proof,
      root := ← checked <| Abi.uintWord first.root,
      nullifierHash := ← checked <| Abi.uintWord first.nullifierHash,
      recipient := first.recipient, fee := first.fee },
    verificationGasLimit := input.verificationGas, callGasLimit := input.executionGas,
    preVerificationGas := input.preVerificationGas,
    paymasterVerificationGasLimit := input.paymasterVerificationGas,
    paymasterPostOpGasLimit := input.postOpGas,
    maxFeePerGas := input.maxFee, maxPriorityFeePerGas := input.priorityFee }

def main : IO UInt32 := do
  let original ← operation intent
  let certificate ← checked <| accept intent original
  require (certificate.output.withdrawals.size == 2 && certificate.output.calls.size == 4)
    "Ordered withdrawal prefix or exact reviewed tail was lost."
  let reject (input : Intent) (changed : UserOperation) : IO Unit :=
    require (!(accept input changed).isOk) "An unauthorized batch mutation was accepted."
  let rejectCalls (input : Intent) (base : UserOperation) (calls : Array Abi.ContractCall) : IO Unit := do
    reject input { base with callData := ← checked <| Abi.accountExecuteBatchComposed calls }
  let calls := certificate.output.calls
  for changed in #[
    { original with sender := 8 }, { original with nonce := 8 },
    { original with factory := some (.address 8) },
    { original with factory := some .eip7702Marker },
    { original with factoryData := ByteArray.mk #[0] },
    { original with authorizationAddress := some 8 },
    { original with paymaster := some 8 }, { original with paymaster := none },
    { original with paymasterSignature := some ByteArray.empty },
    { original with signature := ByteArray.mk #[0] },
    { original with verificationGasLimit := 8 }, { original with callGasLimit := 8 },
    { original with preVerificationGas := 8 },
    { original with paymasterVerificationGasLimit := 8 },
    { original with paymasterPostOpGasLimit := 8 },
    { original with maxFeePerGas := 8 }, { original with maxPriorityFeePerGas := 8 },
    { original with callData := original.callData.push 0 },
    { original with paymasterData := original.paymasterData.push 0 }] do reject intent changed
  let sponsor := certificate.output.sponsor
  for changed in #[
    { sponsor with instanceAddress := 8 }, { sponsor with recipient := 8 },
    { sponsor with fee := 8 }, { sponsor with proof := sponsor.proof.set! 0 12 },
    { sponsor with root := ← checked <| Abi.uintWord 8 },
    { sponsor with nullifierHash := ← checked <| Abi.uintWord 8 }] do
    reject intent { original with paymasterData := ← checked <| Abi.sponsorParameters changed }
  let w := intent.notes[1]!.withdrawal
  for changed in #[
    { w with pool := 8 }, { w with proof := w.proof.set! 0 12 },
    { w with root := 8 }, { w with nullifierHash := 8 },
    { w with recipient := 8 }, { w with relayer := 8 },
    { w with fee := 1 }, { w with refund := 1 }] do
    rejectCalls intent original (calls.set! 0 (← withdrawalCall changed))
  rejectCalls intent original (calls.set! 0 { calls[0]! with value := 1 })
  rejectCalls intent original #[calls[1]!, calls[0]!, calls[2]!, calls[3]!]
  rejectCalls intent original #[calls[0]!, calls[1]!, calls[3]!, calls[2]!]
  rejectCalls intent original (calls.extract 1 calls.size)
  rejectCalls intent original (calls.push calls[2]!)
  rejectCalls intent original (#[← withdrawalCall intent.notes[0]!.withdrawal] ++ calls)
  rejectCalls intent original (calls.set! 2 { calls[2]! with value := 4 })
  rejectCalls intent original (calls.set! 2 { calls[2]! with data := ByteArray.mk #[0x12] })
  rejectCalls intent original (calls.set! 2 { calls[2]! with to := 12 })
  reject intent { original with callData := calls[0]!.data }
  require (!(accept intent original { maxCallGas := 1 }).isOk)
    "The selected maximum gas policy was ignored."
  let undeployed := { intent with deployed := false }
  let deployment ← operation undeployed
  let _ ← checked <| accept undeployed deployment
  reject undeployed { deployment with factory := none }
  reject undeployed { deployment with factory := some (.address 8) }
  reject undeployed { deployment with factoryData := ← checked <|
    Tornado.SmartAccount.accountFactoryData 8 }
  reject undeployed { deployment with factoryData := deployment.factoryData.push 0 }
  let eth := { intent with tail := #[], receiver := 8 }
  let forwarded ← operation eth
  let ethChecked ← checked <| accept eth forwarded
  let ethCalls := ethChecked.output.calls
  require (ethCalls[2]!.value == 5993) "Mixed denomination ETH net forwarding is incorrect."
  for changed in #[
    { ethCalls[2]! with to := 9 }, { ethCalls[2]! with value := 5994 },
    { ethCalls[2]! with data := ByteArray.mk #[0] }] do
    rejectCalls eth forwarded (ethCalls.set! 2 changed)
  rejectCalls eth forwarded (ethCalls.extract 0 2)
  rejectCalls eth forwarded (ethCalls.push ethCalls[2]!)
  let token := { eth with token := some 10 }
  let tokenOp ← operation token
  let tokenChecked ← checked <| accept token tokenOp
  let tokenCalls := tokenChecked.output.calls
  for changed in #[
    { tokenCalls[2]! with to := 9 }, { tokenCalls[2]! with value := 1 },
    { tokenCalls[2]! with data := ← checked <| Abi.erc20Transfer 9 5993 },
    { tokenCalls[2]! with data := ← checked <| Abi.erc20Transfer 8 5994 },
    { tokenCalls[2]! with data := tokenCalls[2]!.data.push 0 }] do
    rejectCalls token tokenOp (tokenCalls.set! 2 changed)
  let retained := { intent with tail := #[] }
  let retainedOp ← operation retained
  let _ ← checked <| accept retained retainedOp
  rejectCalls retained retainedOp (calls.extract 0 3)
  let one := { intent with notes := #[intent.notes[0]!] }
  let _ ← checked <| accept one (← operation one)
  let oneWithoutCalls := { eth with notes := #[intent.notes[0]!] }
  reject oneWithoutCalls (← operation oneWithoutCalls)
  let twelve := { intent with
    notes := #[intent.notes[0]!] ++ (List.range 11).toArray.map
      (fun i => note (20 + i) (50 + i) (100 + i) (1000 + i)),
    tail := (List.range 12).toArray.map
      (fun i => ({ to := 200 + i, value := i, data := ByteArray.empty } : Abi.ContractCall)) }
  let maximum ← checked <| accept twelve (← operation twelve)
  require (maximum.output.calls.size == 23) "Eleven withdrawal plus twelve user calls were rejected."
  let thirteenCalls := { twelve with tail := twelve.tail.push twelve.tail[0]! }
  reject thirteenCalls (← operation thirteenCalls)
  let changeRequest (index : Nat) (withdrawal : Withdrawal) : Intent :=
    { intent with notes := intent.notes.set! index { intent.notes[index]! with withdrawal } }
  let first := intent.notes[0]!.withdrawal
  let invalidRequests := #[
    changeRequest 0 { first with fee := 0 },
    changeRequest 0 { first with fee := 1000 },
    changeRequest 0 { first with relayer := 0 },
    changeRequest 0 { first with refund := 1 },
    changeRequest 1 { w with relayer := 4 },
    changeRequest 1 { w with fee := 1 },
    changeRequest 1 { w with refund := 1 },
    changeRequest 1 { w with nullifierHash := first.nullifierHash },
    { intent with notes := intent.notes.set! 1 { intent.notes[1]! with denomination := 0 } },
    { intent with owner := 0 }, { intent with owner := Abi.maxAddress },
    { intent with receiver := 8 },
    { intent with tail := #[{ to := intent.account, value := 0, data := ByteArray.empty }] },
    { twelve with notes := twelve.notes.push (note 300 400 500 1000) }]
  for invalid in invalidRequests do reject invalid (← operation invalid)
  IO.println "PASS: decoded batch intent, exact ordered calls, deployment, ETH/ERC-20 net forwarding, gas policy, and mutation rejection"
  return 0
