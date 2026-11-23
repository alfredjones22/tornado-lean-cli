import Tornado.Protocol.DirectWithdrawalIntent

/-! Encoding-boundary mutations, using synthetic public bytes only. The
gate does not claim these bytes are a valid cryptographic proof. -/

open Tornado.Protocol Tornado.Protocol.UserOperation08
open Tornado.Protocol.DirectWithdrawalIntent

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def main : IO UInt32 := do
  let data : Abi.SponsorData := {
    instanceAddress := 3, recipient := 2, fee := 7,
    proof := ByteArray.mk (Array.replicate 256 11),
    root := ← checked <| Abi.uintWord 13,
    nullifierHash := ← checked <| Abi.uintWord 17 }
  let intent : Intent := {
    sender := 1, sponsor := 4, pool := data.instanceAddress,
    recipient := data.recipient, proof := data.proof, root := data.root,
    nullifierHash := data.nullifierHash, fee := data.fee,
    verificationGas := 50000, preVerificationGas := 100000,
    paymasterVerificationGas := 450000, postOpGas := 50000,
    maxFee := 1000000000, priorityFee := 100000000 }
  let operation : UserOperation := {
    sender := intent.sender, paymaster := some intent.sponsor,
    verificationGasLimit := intent.verificationGas,
    preVerificationGas := intent.preVerificationGas,
    paymasterVerificationGasLimit := intent.paymasterVerificationGas,
    paymasterPostOpGasLimit := intent.postOpGas,
    maxFeePerGas := intent.maxFee, maxPriorityFeePerGas := intent.priorityFee,
    paymasterData := ← checked <| Abi.sponsorParameters data }
  let result ← checked <| accept intent operation
  require (result.sponsorData == data) "The decoded reviewed sponsor tuple changed."
  let reject (changed : UserOperation) : IO Unit :=
    require (!(accept intent changed).isOk) "An unreviewed operation mutation was accepted."
  let changedData ← #[
    { data with recipient := 8 }, { data with instanceAddress := 8 },
    { data with fee := 8 }, { data with proof := data.proof.set! 0 12 },
    { data with root := ← checked <| Abi.uintWord 8 },
    { data with nullifierHash := ← checked <| Abi.uintWord 8 }].mapM fun changed =>
      checked <| Abi.sponsorParameters changed
  for bytes in changedData do reject { operation with paymasterData := bytes }
  for changed in #[
    { operation with sender := 8 }, { operation with nonce := 1 },
    { operation with callData := ByteArray.mk #[0] },
    { operation with callGasLimit := 1 }, { operation with paymaster := some 8 },
    { operation with factory := some (.address 8) },
    { operation with factoryData := ByteArray.mk #[0] },
    { operation with authorizationAddress := some 8 },
    { operation with paymasterSignature := some ByteArray.empty },
    { operation with verificationGasLimit := 8 },
    { operation with preVerificationGas := 8 },
    { operation with paymasterVerificationGasLimit := 8 },
    { operation with paymasterPostOpGasLimit := 8 },
    { operation with maxFeePerGas := 8 },
    { operation with maxPriorityFeePerGas := 8 },
    { operation with paymasterData := operation.paymasterData.push 0 }] do reject changed
  IO.println "PASS: decoded direct withdrawal intent, canonical sponsor bytes, and 22 unauthorized mutations"
  return 0
