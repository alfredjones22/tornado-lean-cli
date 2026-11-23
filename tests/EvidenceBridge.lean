import Tornado.Policy.EvidenceBridge

open Tornado.Policy.EvidenceBridge Tornado.Protocol.Events

private def word (n : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:32] do
    result := result.push ((n / 256 ^ (31 - i) % 256).toUInt8)
  return result

private def require (condition : Bool) (label : String) : Except String Unit :=
  if condition then .ok () else .error s!"Evidence bridge check failed: {label}."

private def check : Except String Unit := do
  let operationHash := word 10
  let nullifierOne := word 11
  let nullifierTwo := word 12
  let entry : ExpectedEntry := {
    entryPoint := 21, userOpHash := operationHash, sender := 22,
    paymaster := 23, nonce := 2 }
  let withdrawalOne : ExpectedWithdrawal := {
    pool := 20, recipient := 24, nullifierHash := nullifierOne,
    relayer := 25, fee := 26 }
  let withdrawalTwo : ExpectedWithdrawal := {
    pool := 20, recipient := 24, nullifierHash := nullifierTwo,
    relayer := 25, fee := 0 }
  let entryLog : Log := {
    address := entry.entryPoint,
    topics := #[userOperationTopic, operationHash, word entry.sender, word entry.paymaster],
    data := word entry.nonce ++ word 1 ++ word 100 ++ word 1000 }
  let withdrawalLogOne : Log := {
    address := withdrawalOne.pool,
    topics := #[withdrawalTopic, word withdrawalOne.relayer],
    data := word withdrawalOne.recipient ++ nullifierOne ++ word withdrawalOne.fee }
  let withdrawalLogTwo : Log := {
    address := withdrawalTwo.pool,
    topics := #[withdrawalTopic, word withdrawalTwo.relayer],
    data := word withdrawalTwo.recipient ++ nullifierTwo ++ word withdrawalTwo.fee }
  let logs := [entryLog, withdrawalLogOne, withdrawalLogTwo]
  let direct : Tornado.Policy.Attempt := {
    phase := .submitted,
    reviewedHash := some (hashText operationHash),
    signedHash := some (hashText operationHash),
    reservedHash := some (hashText operationHash),
    sends := 1 }
  let selected := withdrawalTexts [withdrawalOne, withdrawalTwo]
  let batch : Tornado.Policy.Batch.Attempt := {
    phase := .submitted, selected,
    reviewedHash := some (hashText operationHash),
    signedHash := some (hashText operationHash), reserved := selected,
    sends := 1 }
  require ((confirmDirect direct true logs entry withdrawalOne).isOk)
    "exact direct receipt"
  require ((confirmBatch batch true logs entry [withdrawalOne, withdrawalTwo]).isOk)
    "exact batch receipt"
  require (!(confirmDirect direct false logs entry withdrawalOne).isOk)
    "reverted direct receipt"
  require (!(confirmBatch batch false logs entry [withdrawalOne, withdrawalTwo]).isOk)
    "reverted batch receipt"
  require (!(confirmDirect direct true [entryLog] entry withdrawalOne).isOk)
    "missing direct withdrawal"
  require (!(confirmBatch batch true [entryLog, withdrawalLogOne] entry [withdrawalOne, withdrawalTwo]).isOk)
    "missing batch withdrawal"
  require (!(confirmDirect direct true (entryLog :: logs) entry withdrawalOne).isOk)
    "ambiguous direct EntryPoint evidence"
  require (!(confirmBatch batch true (entryLog :: logs) entry [withdrawalOne, withdrawalTwo]).isOk)
    "ambiguous batch EntryPoint evidence"
  require (!(confirmDirect { direct with signedHash := some "0x00" }
    true logs entry withdrawalOne).isOk) "direct signed hash mismatch"
  require (!(confirmBatch { batch with signedHash := some "0x00" }
    true logs entry [withdrawalOne, withdrawalTwo]).isOk) "batch signed hash mismatch"
  require (!(confirmBatch { batch with selected := [selected.head!] }
    true logs entry [withdrawalOne, withdrawalTwo]).isOk) "selected notes mismatch"
  require (!(confirmBatch batch true logs entry [withdrawalOne, withdrawalOne]).isOk)
    "duplicate expected nullifier"
  require (!(confirmDirect direct true logs
    { entry with nonce := 3 } withdrawalOne).isOk) "wrong EntryPoint nonce"
  require (!(confirmDirect direct true logs entry
    { withdrawalOne with pool := 99 }).isOk) "wrong pool"
  require (!(confirmDirect { direct with phase := .fresh }
    true logs entry withdrawalOne).isOk) "invalid policy phase"
  return ()

def main : IO UInt32 := do
  match check with
  | .ok _ =>
    IO.println "PASS: exact one-note and batch event-to-policy bridge, 15 checks"
    return 0
  | .error error =>
    IO.eprintln error
    return 1
