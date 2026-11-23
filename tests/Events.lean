import Lean
import Tornado.Protocol.Events

open Lean Tornado.Crypto Tornado.Protocol.Events

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def textField (json : Json) (name : String) : Except String String :=
  (field json name).bind Json.getStr?

private def natField (json : Json) (name : String) : Except String Nat := do
  let raw ← textField json name
  let some value := raw.toNat? | throw s!"Invalid decimal event fixture: {name}."
  return value

private def hexNibble (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

private def hexBytes (raw : String) : Except String ByteArray := do
  if !raw.startsWith "0x" || (raw.length - 2) % 2 != 0 then
    throw "Invalid hex event fixture."
  let chars := (raw.toList.drop 2).toArray
  let mut bytes := ByteArray.empty
  for i in [0:chars.size / 2] do
    let some hi := hexNibble chars[2 * i]! | throw "Invalid high hex nibble."
    let some lo := hexNibble chars[2 * i + 1]! | throw "Invalid low hex nibble."
    bytes := bytes.push (hi * 16 + lo).toUInt8
  return bytes

private def addressNat (raw : String) : Except String Nat := do
  let bytes ← hexBytes raw
  if bytes.size != 20 then throw "Fixture address must have 20 bytes."
  return bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def parseLog (json : Json) : Except String Log := do
  let address ← addressNat (← textField json "address")
  let rawTopics ← (← field json "topics").getArr?
  let mut topics := #[]
  for raw in rawTopics do topics := topics.push (← hexBytes (← raw.getStr?))
  return { address, topics, data := (← hexBytes (← textField json "data")) }

private def withByte (bytes : ByteArray) (index : Nat) (value : UInt8) : ByteArray :=
  ByteArray.mk (bytes.data.set! index value)

private def require (ok : Bool) (label : String) : Except String Unit :=
  if ok then .ok () else .error s!"Event check failed: {label}."

private def checkVectors (root : Json) : Except String (Nat × Nat) := do
  require ((← textField root "viemVersion") == "2.55.19") "oracle version"
  let logs ← field root "logs"
  let depositLog ← parseLog (← field logs "deposit")
  let secondDepositLog ← parseLog (← field logs "depositTwo")
  let withdrawalLog ← parseLog (← field logs "withdrawal")
  let secondWithdrawalLog ← parseLog (← field logs "withdrawalTwo")
  let entryLog ← parseLog (← field logs "entry")
  let failedEntryLog ← parseLog (← field logs "failedEntry")
  let depositEntryLog ← parseLog (← field logs "depositEntry")
  let expected ← field root "expected"
  let depositExpected ← field expected "deposit"
  let withdrawalExpected ← field expected "withdrawal"
  let entryExpected ← field expected "entry"
  let deposit ← decodeDeposit depositLog
  let secondDeposit ← decodeDeposit secondDepositLog
  let withdrawal ← decodeWithdrawal withdrawalLog
  let secondWithdrawal ← decodeWithdrawal secondWithdrawalLog
  let entry ← decodeUserOperationEvent entryLog
  let failedEntry ← decodeUserOperationEvent failedEntryLog
  let expectedDeposit : ExpectedDeposit := {
    pool := depositLog.address,
    commitment := (← hexBytes (← textField depositExpected "commitment")) }
  let secondExpectedDeposit : ExpectedDeposit := {
    pool := secondDepositLog.address, commitment := secondDeposit.commitment }
  let expectedWithdrawal : ExpectedWithdrawal := {
    pool := withdrawalLog.address,
    recipient := (← addressNat (← textField withdrawalExpected "recipient")),
    nullifierHash := (← hexBytes (← textField withdrawalExpected "nullifierHash")),
    relayer := (← addressNat (← textField withdrawalExpected "relayer")),
    fee := (← natField withdrawalExpected "fee") }
  let secondExpected : ExpectedWithdrawal := {
    pool := secondWithdrawalLog.address,
    recipient := expectedWithdrawal.recipient,
    nullifierHash := secondWithdrawal.nullifierHash,
    relayer := expectedWithdrawal.relayer,
    fee := secondWithdrawal.fee }
  let expectedEntry : ExpectedEntry := {
    entryPoint := entryLog.address,
    userOpHash := (← hexBytes (← textField entryExpected "userOpHash")),
    sender := (← addressNat (← textField entryExpected "sender")),
    paymaster := (← addressNat (← textField entryExpected "paymaster")),
    nonce := (← natField entryExpected "nonce") }
  let depositExpectedEntry : ExpectedEntry := { expectedEntry with paymaster := 0 }
  let exact : List (String × Bool) := [
    ("Deposit topic", depositLog.topics[0]! == depositTopic),
    ("Withdrawal topic", withdrawalLog.topics[0]! == withdrawalTopic),
    ("UserOperationEvent topic", entryLog.topics[0]! == userOperationTopic),
    ("Deposit commitment", deposit.commitment == expectedDeposit.commitment),
    ("Deposit leafIndex", deposit.leafIndex == (← natField depositExpected "leafIndex")),
    ("Deposit timestamp", deposit.timestamp == (← natField depositExpected "timestamp")),
    ("second Deposit commitment", secondDeposit.commitment == (ByteArray.mk (Array.replicate 32 0xee))),
    ("second Deposit leafIndex", secondDeposit.leafIndex == 8),
    ("second Deposit timestamp", secondDeposit.timestamp == 123457),
    ("Withdrawal recipient", withdrawal.recipient == expectedWithdrawal.recipient),
    ("Withdrawal nullifier", withdrawal.nullifierHash == expectedWithdrawal.nullifierHash),
    ("Withdrawal relayer", withdrawal.relayer == expectedWithdrawal.relayer),
    ("Withdrawal fee", withdrawal.fee == expectedWithdrawal.fee),
    ("EntryPoint hash", entry.userOpHash == expectedEntry.userOpHash),
    ("EntryPoint sender", entry.sender == expectedEntry.sender),
    ("EntryPoint paymaster", entry.paymaster == expectedEntry.paymaster),
    ("EntryPoint nonce", entry.nonce == expectedEntry.nonce),
    ("EntryPoint success", entry.success == (← (← field entryExpected "success").getBool?)),
    ("EntryPoint actualGasCost", entry.actualGasCost == (← natField entryExpected "actualGasCost")),
    ("EntryPoint actualGasUsed", entry.actualGasUsed == (← natField entryExpected "actualGasUsed")),
    ("failed EntryPoint event", !failedEntry.success),
    ("zero-paymaster batch Deposit EntryPoint", (← decodeUserOperationEvent depositEntryLog).paymaster == 0),
    ("second withdrawal nullifier", secondWithdrawal.nullifierHash == secondExpected.nullifierHash),
    ("second withdrawal zero fee", secondWithdrawal.fee == 0)
  ]
  for (name, ok) in exact do require ok name
  let receipt := [entryLog, withdrawalLog, secondWithdrawalLog]
  let accepted : List (String × Bool) := [
    ("deposit receipt", hasDeposit [depositLog] expectedDeposit),
    ("direct Deposit receipt confirmed", directDepositOutcome true [depositLog] expectedDeposit == .confirmed),
    ("batch Deposit receipt confirmed", batchDepositOutcome true [depositEntryLog, depositLog, secondDepositLog]
      depositExpectedEntry [expectedDeposit, secondExpectedDeposit] == .confirmed),
    ("withdrawal receipt", hasWithdrawal receipt expectedWithdrawal),
    ("unique EntryPoint success", uniqueEntryResult receipt expectedEntry == some true),
    ("direct receipt confirmed", directOutcome true receipt expectedEntry expectedWithdrawal == .confirmed),
    ("batch receipt confirmed", batchOutcome true receipt expectedEntry [expectedWithdrawal, secondExpected] == .confirmed),
    ("matching EntryPoint failure", directOutcome true [failedEntryLog] expectedEntry expectedWithdrawal == .failed),
    ("matching batch failure", batchOutcome true [failedEntryLog] expectedEntry [expectedWithdrawal, secondExpected] == .failed)
  ]
  for (name, ok) in accepted do require ok name
  let wrongTopic := withByte depositLog.topics[0]! 0 0
  let wrongSignature := { depositLog with topics := depositLog.topics.set! 0 wrongTopic }
  let badLeaf := { depositLog with data := withByte depositLog.data 0 1 }
  let shortDeposit := { depositLog with data := depositLog.data.extract 0 63 }
  let extraDeposit := { depositLog with data := depositLog.data.push 0 }
  let shortTopic := { depositLog with topics := depositLog.topics.set! 1 (depositLog.topics[1]!.extract 0 31) }
  let badRecipient := { withdrawalLog with data := withByte withdrawalLog.data 0 1 }
  let badRelayer := { withdrawalLog with topics := withdrawalLog.topics.set! 1 (withByte withdrawalLog.topics[1]! 0 1) }
  let badBool := { entryLog with data := withByte entryLog.data 63 2 }
  let badSender := { entryLog with topics := entryLog.topics.set! 2 (withByte entryLog.topics[2]! 0 1) }
  let badPaymaster := { entryLog with topics := entryLog.topics.set! 3 (withByte entryLog.topics[3]! 0 1) }
  let rejected : List (String × Bool) := [
    ("spoofed Deposit pool", !hasDeposit [{ depositLog with address := withdrawalLog.address }] expectedDeposit),
    ("wrong Deposit commitment", !hasDeposit [depositLog] { expectedDeposit with commitment := entry.userOpHash }),
    ("missing direct Deposit event", directDepositOutcome true [] expectedDeposit == .unknown),
    ("reverted direct Deposit receipt", directDepositOutcome false [depositLog] expectedDeposit == .failed),
    ("missing batch Deposit event", batchDepositOutcome true [depositEntryLog, depositLog]
      depositExpectedEntry [expectedDeposit, secondExpectedDeposit] == .unknown),
    ("duplicate expected batch Deposit", batchDepositOutcome true [depositEntryLog, depositLog]
      depositExpectedEntry [expectedDeposit, expectedDeposit] == .unknown),
    ("empty batch Deposit", batchDepositOutcome true [depositEntryLog] depositExpectedEntry [] == .unknown),
    ("batch Deposit must have zero paymaster", batchDepositOutcome true [entryLog, depositLog]
      expectedEntry [expectedDeposit] == .unknown),
    ("reverted batch Deposit receipt", batchDepositOutcome false [depositEntryLog, depositLog]
      depositExpectedEntry [expectedDeposit] == .failed),
    ("wrong Deposit signature", !(decodeDeposit wrongSignature).isOk),
    ("Deposit uint32 overflow", !(decodeDeposit badLeaf).isOk),
    ("short Deposit data", !(decodeDeposit shortDeposit).isOk),
    ("extra Deposit data", !(decodeDeposit extraDeposit).isOk),
    ("short indexed topic", !(decodeDeposit shortTopic).isOk),
    ("extra Deposit topic", !(decodeDeposit { depositLog with topics := depositLog.topics.push depositTopic }).isOk),
    ("oversized emitting address", !(decodeDeposit { depositLog with address := 2 ^ 160 }).isOk),
    ("noncanonical Withdrawal recipient", !(decodeWithdrawal badRecipient).isOk),
    ("noncanonical Withdrawal relayer", !(decodeWithdrawal badRelayer).isOk),
    ("spoofed withdrawal pool", !hasWithdrawal [{ withdrawalLog with address := depositLog.address }] expectedWithdrawal),
    ("wrong withdrawal recipient", !hasWithdrawal receipt { expectedWithdrawal with recipient := depositLog.address }),
    ("wrong withdrawal nullifier", !hasWithdrawal receipt { expectedWithdrawal with nullifierHash := entry.userOpHash }),
    ("wrong withdrawal relayer", !hasWithdrawal receipt { expectedWithdrawal with relayer := depositLog.address }),
    ("wrong withdrawal fee", !hasWithdrawal receipt { expectedWithdrawal with fee := 1001 }),
    ("noncanonical EntryPoint boolean", !(decodeUserOperationEvent badBool).isOk),
    ("noncanonical EntryPoint sender", !(decodeUserOperationEvent badSender).isOk),
    ("noncanonical EntryPoint paymaster", !(decodeUserOperationEvent badPaymaster).isOk),
    ("spoofed EntryPoint address", uniqueEntryResult [{ entryLog with address := depositLog.address }] expectedEntry == none),
    ("wrong UserOperation hash", uniqueEntryResult receipt { expectedEntry with userOpHash := deposit.commitment } == none),
    ("wrong sender", uniqueEntryResult receipt { expectedEntry with sender := depositLog.address } == none),
    ("wrong paymaster", uniqueEntryResult receipt { expectedEntry with paymaster := depositLog.address } == none),
    ("wrong nonce", uniqueEntryResult receipt { expectedEntry with nonce := 43 } == none),
    ("duplicate EntryPoint evidence", uniqueEntryResult [entryLog, entryLog] expectedEntry == none),
    ("conflicting EntryPoint evidence", uniqueEntryResult [entryLog, failedEntryLog] expectedEntry == none),
    ("receipt failure cannot confirm", directOutcome false receipt expectedEntry expectedWithdrawal == .unknown),
    ("missing withdrawal cannot confirm", directOutcome true [entryLog] expectedEntry expectedWithdrawal == .unknown),
    ("missing batch withdrawal cannot confirm", batchOutcome true [entryLog, withdrawalLog] expectedEntry [expectedWithdrawal, secondExpected] == .unknown),
    ("duplicate batch nullifier cannot confirm", batchOutcome true receipt expectedEntry [expectedWithdrawal, expectedWithdrawal] == .unknown),
    ("empty batch cannot confirm", batchOutcome true receipt expectedEntry [] == .unknown),
    ("overlarge batch cannot confirm", batchOutcome true receipt expectedEntry (List.replicate 13 expectedWithdrawal) == .unknown)
  ]
  for (name, ok) in rejected do require ok name
  return (exact.length + accepted.length, rejected.length)

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/events-vectors.json"
  match Json.parse raw >>= checkVectors with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok (matched, rejected) =>
      IO.println s!"PASS: 7 viem event vectors, {matched} exact-evidence checks, {rejected} malformed/spoofed/rejection checks"
      return 0
