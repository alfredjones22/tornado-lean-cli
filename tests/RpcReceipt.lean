import Lean
import Tornado.Domain.NoteIdentity
import Tornado.Protocol.RpcReceipt

open Lean Tornado.Domain Tornado.Protocol.Events
open Tornado.Protocol.RpcReceipt

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def string (json : Json) (name : String) : Except String String := do
  (← field json name).getStr?

private def fixedHex (raw : String) (length : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw "Fixture hex lacks prefix."
  let bytes ← parseHexBytes raw
  if bytes.size != length then throw "Fixture hex has wrong width."
  return bytes

private def hashField (json : Json) (name : String) : Except String ByteArray :=
  (string json name).bind (fixedHex · 32)

private def addressField (json : Json) (name : String) : Except String Nat := do
  let bytes ← (string json name).bind (fixedHex · 20)
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def quantityField (json : Json) (name : String) : Except String Nat :=
  (string json name).bind quantity

private def replace (json : Json) (name : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert name value)
  | other => other

private def require (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def check (root : Json) : Except String (Nat × Nat) := do
  require ((← string root "viemVersion") == "2.55.19") "Wrong viem fixture version."
  let expected ← field root "expected"
  let responses ← field root "responses"
  let expectedTxHash ← hashField expected "transactionHash"
  let failedTxHash ← hashField expected "failedTransactionHash"
  let depositTxHash ← hashField expected "depositTransactionHash"
  let entry : ExpectedEntry := {
    entryPoint := (← addressField expected "entryPoint"),
    userOpHash := (← hashField expected "userOpHash"),
    sender := (← addressField expected "sender"),
    paymaster := (← addressField expected "paymaster"),
    nonce := (← quantityField expected "nonce") }
  let withdrawal : ExpectedWithdrawal := {
    pool := (← addressField expected "pool"),
    recipient := (← addressField expected "recipient"),
    nullifierHash := (← hashField expected "nullifierHash"),
    relayer := (← addressField expected "relayer"),
    fee := (← quantityField expected "fee") }
  let deposit : ExpectedDeposit := {
    pool := (← addressField expected "depositPool"),
    commitment := (← hashField expected "commitment") }
  let chainJson ← field responses "chain"
  let bundlerJson ← field responses "bundler"
  let failedChainJson ← field responses "failedChain"
  let failedBundlerJson ← field responses "failedBundler"
  let depositJson ← field responses "depositChain"
  let some chain ← parseChainResponse chainJson 7 expectedTxHash
    | throw "Missing direct receipt fixture."
  let some bundler ← parseBundlerResponse bundlerJson 8 entry
    | throw "Missing bundler receipt fixture."
  let some failedChain ← parseChainResponse failedChainJson 9 failedTxHash
    | throw "Missing failed operation chain fixture."
  let some failedBundler ← parseBundlerResponse failedBundlerJson 10 entry
    | throw "Missing failed operation bundler fixture."
  let some depositChain ← parseChainResponse depositJson 11 depositTxHash
    | throw "Missing deposit receipt fixture."
  let batchDepositTxHash ← hashField expected "batchDepositTransactionHash"
  let relayerTxHash ← hashField expected "relayerTransactionHash"
  let some batchDepositChain ← parseChainResponse (← field responses "batchDepositChain") 13 batchDepositTxHash
    | throw "Missing batch deposit receipt fixture."
  let some relayerChain ← parseChainResponse (← field responses "relayerChain") 14 relayerTxHash
    | throw "Missing relayer receipt fixture."
  let some secondDepositLog := batchDepositChain.logs[2]?
    | throw "Batch deposit receipt lost its second pool event."
  let secondDepositEvent ← decodeDeposit secondDepositLog
  let secondDeposit : ExpectedDeposit :=
    ⟨deposit.pool, secondDepositEvent.commitment⟩
  let batchEntry := { entry with paymaster := 0 }
  let formatter ← field root "viemFormatterSummary"
  let exact : List (String × Bool) := [
    ("viem chain status", (← string formatter "receiptStatus") == "success"),
    ("viem user operation status", (← string formatter "userOperationReceiptStatus") == "success"),
    ("chain hash", chain.transactionHash == expectedTxHash),
    ("chain block hash", chain.blockHash == (← hashField expected "blockHash")),
    ("chain block number", chain.blockNumber == (← quantityField expected "blockNumber")),
    ("chain logs", chain.logs.length == 2),
    ("direct outcome", directWithdrawalOutcome chain expectedTxHash entry withdrawal (some bundler) == .confirmed),
    ("batch outcome", batchWithdrawalOutcome chain expectedTxHash entry [withdrawal] (some bundler) == .confirmed),
    ("direct chain-only outcome", directWithdrawalOutcome chain expectedTxHash entry withdrawal none == .confirmed),
    ("failed user operation", directWithdrawalOutcome failedChain failedTxHash entry withdrawal (some failedBundler) == .failed),
    ("deposit outcome", depositOutcome depositChain depositTxHash deposit == .confirmed),
    ("batch deposit outcome", batchDepositOutcome batchDepositChain batchDepositTxHash
      batchEntry [deposit, secondDeposit] none == .confirmed),
    ("relayer withdrawal outcome", relayerWithdrawalOutcome relayerChain relayerTxHash withdrawal == .confirmed),
    ("pending bundler", (← parseBundlerResponse (← field responses "pendingBundler") 12 entry).isNone),
    ("bundler hash", bundler.transactionHash == expectedTxHash),
    ("bundler user operation", bundler.userOpHash == entry.userOpHash)
  ]
  for (name, passed) in exact do require passed name

  let receiptJson ← field chainJson "result"
  let rawLogs ← (← field receiptJson "logs").getArr?
  let log0 := rawLogs[0]!
  let log1 := rawLogs[1]!
  let badLogHash := replace log0 "transactionHash" (toJson (← string expected "failedTransactionHash"))
  let badBlockHash := replace log0 "blockHash" (toJson (← string expected "transactionHash"))
  let badBlockNumber := replace log0 "blockNumber" (toJson "0x1235")
  let duplicateIndex := replace log1 "logIndex" (toJson "0x0")
  let badAddress := replace log0 "address" (toJson "0x1234")
  let badTopic := replace log0 "topics" (toJson #["0x1234"])
  let alteredLog (changed : Json) : Json :=
    replace chainJson "result" (replace receiptJson "logs" (toJson (rawLogs.set! 0 changed)))
  let alteredSecond (changed : Json) : Json :=
    replace chainJson "result" (replace receiptJson "logs" (toJson (rawLogs.set! 1 changed)))
  let alteredReceipt (name : String) (changed : Json) : Json :=
    replace chainJson "result" (replace receiptJson name changed)
  let badBundler := replace bundlerJson "result"
    (replace (← field bundlerJson "result") "userOpHash"
      (toJson (← string expected "transactionHash")))
  let badPaymaster := replace bundlerJson "result"
    (replace (← field bundlerJson "result") "paymaster"
      (toJson (← string expected "sender")))
  let rejected : List (String × Bool) := [
    ("wrong response ID", !(parseChainResponse (replace chainJson "id" (toJson (8 : Nat))) 7 expectedTxHash).isOk),
    ("wrong JSON-RPC version", !(parseChainResponse (replace chainJson "jsonrpc" (toJson "1.0")) 7 expectedTxHash).isOk),
    ("wrong receipt hash", !(parseChainResponse chainJson 7 failedTxHash).isOk),
    ("noncanonical status", !(parseChainResponse (alteredReceipt "status" (toJson "0x01")) 7 expectedTxHash).isOk),
    ("missing logs", !(parseChainResponse (alteredReceipt "logs" Json.null) 7 expectedTxHash).isOk),
    ("noncanonical block quantity", !(parseChainResponse (alteredReceipt "blockNumber" (toJson "0x01234")) 7 expectedTxHash).isOk),
    ("wrong log transaction hash", !(parseChainResponse (alteredLog badLogHash) 7 expectedTxHash).isOk),
    ("wrong log block hash", !(parseChainResponse (alteredLog badBlockHash) 7 expectedTxHash).isOk),
    ("wrong log block number", !(parseChainResponse (alteredLog badBlockNumber) 7 expectedTxHash).isOk),
    ("removed log", !(parseChainResponse (alteredLog (replace log0 "removed" (toJson true))) 7 expectedTxHash).isOk),
    ("duplicate log index", !(parseChainResponse (alteredSecond duplicateIndex) 7 expectedTxHash).isOk),
    ("short log address", !(parseChainResponse (alteredLog badAddress) 7 expectedTxHash).isOk),
    ("short log topic", !(parseChainResponse (alteredLog badTopic) 7 expectedTxHash).isOk),
    ("wrong bundler operation hash", !(parseBundlerResponse badBundler 8 entry).isOk),
    ("wrong bundler paymaster", !(parseBundlerResponse badPaymaster 8 entry).isOk),
    ("contradictory bundler outcome", directWithdrawalOutcome chain expectedTxHash entry withdrawal
      (some { bundler with success := false }) == .unknown),
    ("wrong receipt destination", directWithdrawalOutcome
      { chain with to := some withdrawal.pool } expectedTxHash entry withdrawal (some bundler) == .unknown),
    ("wrong chain transaction", directWithdrawalOutcome
      { chain with transactionHash := failedTxHash } expectedTxHash entry withdrawal (some bundler) == .unknown),
    ("deposit wrong destination", depositOutcome
      { depositChain with to := some entry.entryPoint } depositTxHash deposit == .unknown),
    ("batch deposit missing second event", batchDepositOutcome
      { batchDepositChain with logs := batchDepositChain.logs.take 2 }
      batchDepositTxHash batchEntry [deposit, secondDeposit] none == .unknown),
    ("relayer wrong destination", relayerWithdrawalOutcome
      { relayerChain with to := some entry.entryPoint } relayerTxHash withdrawal == .unknown)
  ]
  for (name, passed) in rejected do require passed name
  return (exact.length, rejected.length)

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/rpc-receipt-vectors.json"
  match Json.parse raw >>= check with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok (exact, rejected) =>
      IO.println s!"PASS: {exact} viem-formatted RPC receipt checks and {rejected} rejection checks"
      return 0
