import Tornado.Spec.EffectRefinement

open Tornado.Spec.Effects Tornado.Protocol.Events

private def word (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:32] do
    out := out.push ((n / 256 ^ (31 - i) % 256).toUInt8)
  return out

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check : Except String Unit := do
  let operationHash := word 10
  let candidate := Tornado.Policy.EvidenceBridge.hashText operationHash
  let nullifier := word 11
  let entry : ExpectedEntry := {
    entryPoint := 21, userOpHash := operationHash, sender := 22,
    paymaster := 23, nonce := 2 }
  let withdrawal : ExpectedWithdrawal := {
    pool := 20, recipient := 24, nullifierHash := nullifier,
    relayer := 25, fee := 26 }
  let config : Config := { chainId := 1, entry, withdrawal }
  let syntheticAuthenticator : Receipt → Bool := fun receipt =>
    receipt.chainId == 1 && receipt.transactionHash == "test-tx"
  let initial : State := {}
  let reviewed ← step config syntheticAuthenticator initial (.review candidate)
  let signed ← step config syntheticAuthenticator reviewed (.sign candidate)
  require (!(step config syntheticAuthenticator signed .expose).isOk)
    "Signed operation exposed without reservation"
  let failedAck : DurableAck := { candidateHash := candidate, durable := false }
  require (!(step config syntheticAuthenticator signed (.reserve failedAck)).isOk)
    "Failed durable write accepted"
  let ack : DurableAck := { candidateHash := candidate, durable := true }
  let reserved ← step config syntheticAuthenticator signed (.reserve ack)
  require (reserved.effects == [.durableReservation candidate])
    "Reservation event missing"
  let exposed ← step config syntheticAuthenticator reserved .expose
  require (exposed.effects == [.durableReservation candidate, .signedExposure candidate])
    "Signed exposure did not follow reservation"
  let submitted ← step config syntheticAuthenticator exposed .send
  require (!(step config syntheticAuthenticator submitted .send).isOk)
    "Second send accepted"
  let uncertain ← step config syntheticAuthenticator submitted .markUnknown
  require (!(step config syntheticAuthenticator uncertain (.review candidate)).isOk)
    "Uncertain attempt allowed new review"
  require (!(step config syntheticAuthenticator uncertain (.sign candidate)).isOk)
    "Uncertain attempt allowed new signature"
  require (!(step config syntheticAuthenticator uncertain .expose).isOk)
    "Uncertain attempt allowed exposure"
  require (!(step config syntheticAuthenticator uncertain .send).isOk)
    "Uncertain attempt allowed send"
  let entryLog : Log := {
    address := entry.entryPoint,
    topics := #[userOperationTopic, operationHash, word entry.sender, word entry.paymaster],
    data := word entry.nonce ++ word 1 ++ word 100 ++ word 1000 }
  let withdrawalLog : Log := {
    address := withdrawal.pool,
    topics := #[withdrawalTopic, word withdrawal.relayer],
    data := word withdrawal.recipient ++ nullifier ++ word withdrawal.fee }
  let receipt : Receipt := {
    chainId := 1, transactionHash := "test-tx", success := true,
    logs := [entryLog, withdrawalLog] }
  require (!(step config (fun _ => false) uncertain (.confirm receipt)).isOk)
    "Unauthenticated receipt accepted"
  require (!(step config syntheticAuthenticator uncertain
    (.confirm { receipt with chainId := 2 })).isOk)
    "Wrong-chain receipt accepted"
  require (!(step config syntheticAuthenticator uncertain
    (.confirm { receipt with logs := [entryLog] })).isOk)
    "Receipt missing pool event accepted"
  let confirmed ← step config syntheticAuthenticator uncertain (.confirm receipt)
  require (confirmed.policy.phase == .confirmed) "Exact authenticated receipt did not confirm"
  require (confirmed.effects.getLast? ==
    some (.authenticatedConfirmation candidate "test-tx"))
    "Authenticated confirmation event missing"

private def checkBatch : Except String Unit := do
  let operationHash := word 30
  let candidate := Tornado.Policy.EvidenceBridge.hashText operationHash
  let firstNullifier := word 31
  let secondNullifier := word 32
  let firstText := Tornado.Policy.EvidenceBridge.hashText firstNullifier
  let secondText := Tornado.Policy.EvidenceBridge.hashText secondNullifier
  let entry : ExpectedEntry := {
    entryPoint := 41, userOpHash := operationHash, sender := 42,
    paymaster := 43, nonce := 5 }
  let first : ExpectedWithdrawal := {
    pool := 44, recipient := 45, nullifierHash := firstNullifier,
    relayer := 46, fee := 47 }
  let second : ExpectedWithdrawal := {
    pool := 44, recipient := 48, nullifierHash := secondNullifier,
    relayer := 46, fee := 49 }
  let config : Batch.Config := {
    chainId := 1, entry, withdrawals := [first, second] }
  let authenticate : Receipt → Bool := fun receipt =>
    receipt.chainId == 1 && receipt.transactionHash == "batch-test-tx"
  let initial : Batch.State := {}
  require (!(Batch.step config authenticate initial
    (.prepare [firstText] candidate)).isOk)
    "Incomplete configured batch selection accepted"
  let prepared ← Batch.step config authenticate initial
    (.prepare [firstText, secondText] candidate)
  let signed ← Batch.step config authenticate prepared (.sign candidate)
  let badAck : Batch.DurableAck := {
    nullifier := firstText, operationHash := candidate, durable := false }
  require (!(Batch.step config authenticate signed (.reserve badAck)).isOk)
    "Failed batch durable reservation accepted"
  let firstAck : Batch.DurableAck := { badAck with durable := true }
  let firstReserved ← Batch.step config authenticate signed (.reserve firstAck)
  require (!(Batch.step config authenticate firstReserved .expose).isOk)
    "Batch exposed before all selected notes were reserved"
  let secondAck : Batch.DurableAck := {
    nullifier := secondText, operationHash := candidate, durable := true }
  let allReserved ← Batch.step config authenticate firstReserved (.reserve secondAck)
  require (allReserved.effects ==
    [.durableReservation firstText, .durableReservation secondText])
    "Batch reservation events missing or out of order"
  let exposed ← Batch.step config authenticate allReserved .expose
  require (exposed.effects ==
    [.durableReservation firstText, .durableReservation secondText,
      .signedExposure candidate])
    "Batch exposure did not follow every reservation"
  let submitted ← Batch.step config authenticate exposed .send
  require (!(Batch.step config authenticate submitted .send).isOk)
    "Second batch send accepted"
  let uncertain ← Batch.step config authenticate submitted .markUnknown
  require (!(Batch.step config authenticate uncertain
    (.prepare [firstText, secondText] candidate)).isOk)
    "Uncertain batch allowed a new preparation"
  require (!(Batch.step config authenticate uncertain (.sign candidate)).isOk)
    "Uncertain batch allowed a new signature"
  require (!(Batch.step config authenticate uncertain (.reserve firstAck)).isOk)
    "Uncertain batch allowed a new reservation"
  require (!(Batch.step config authenticate uncertain .send).isOk)
    "Uncertain batch allowed another send"
  let entryLog : Log := {
    address := entry.entryPoint,
    topics := #[userOperationTopic, operationHash, word entry.sender, word entry.paymaster],
    data := word entry.nonce ++ word 1 ++ word 100 ++ word 1000 }
  let firstLog : Log := {
    address := first.pool,
    topics := #[withdrawalTopic, word first.relayer],
    data := word first.recipient ++ firstNullifier ++ word first.fee }
  let secondLog : Log := {
    address := second.pool,
    topics := #[withdrawalTopic, word second.relayer],
    data := word second.recipient ++ secondNullifier ++ word second.fee }
  let receipt : Receipt := {
    chainId := 1, transactionHash := "batch-test-tx", success := true,
    logs := [entryLog, firstLog, secondLog] }
  require (!(Batch.step config (fun _ => false) uncertain (.confirm receipt)).isOk)
    "Unauthenticated batch receipt accepted"
  require (!(Batch.step config authenticate uncertain
    (.confirm { receipt with logs := [entryLog, firstLog] })).isOk)
    "Batch receipt missing one selected withdrawal accepted"
  let confirmed ← Batch.step config authenticate uncertain (.confirm receipt)
  require (confirmed.policy.phase == .confirmed)
    "Exact authenticated batch receipt did not confirm"
  require (confirmed.effects.getLast? ==
    some (.authenticatedConfirmation candidate "batch-test-tx"))
    "Batch confirmation event missing"

def main : IO UInt32 := do
  match check *> checkBatch with
  | .ok _ =>
    IO.println "PASS: one-note and two-note durable-reservation/authenticated-receipt effect traces"
    return 0
  | .error error =>
    IO.eprintln error
    return 1
