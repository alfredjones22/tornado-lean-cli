import Tornado.Cli.DepositMultiSend
import Tornado.Cli.DepositStatus

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Cli

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def reportedBound (failure : Option String) (wei : Nat) : Bool :=
  match failure with
  | none => false
  | some message => (message.splitOn s!"({wei} wei)").length > 1

private def bytes (number count : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:count] do
    result := result.push ((number / 256 ^ (count - 1 - i) % 256).toUInt8)
  return result

private def hex := ProtectedTxSender.hex
private def quantity := ProtectedTxSender.quantity

private def receipt (sender : Nat) (tx : Rlp.Transaction1559)
    (hash : ByteArray) (wrongEvent : Bool) : Json := Id.run do
  let target := tx.to.getD 0
  let blockHash := bytes 17 32
  let commitment := if wrongEvent then bytes 999 32 else tx.data.extract 4 36
  let log := Json.mkObj [
    ("address", toJson (hex (bytes target 20))),
    ("topics", toJson #[hex Events.depositTopic, hex commitment]),
    ("data", toJson (hex (bytes 0 32 ++ bytes 1 32))),
    ("transactionHash", toJson (hex hash)), ("blockHash", toJson (hex blockHash)),
    ("blockNumber", toJson ("0x1" : String)),
    ("transactionIndex", toJson ("0x0" : String)),
    ("logIndex", toJson ("0x0" : String))]
  return Json.mkObj [("transactionHash", toJson (hex hash)),
    ("blockHash", toJson (hex blockHash)), ("blockNumber", toJson ("0x1" : String)),
    ("transactionIndex", toJson ("0x0" : String)),
    ("from", toJson (hex (bytes sender 20))),
    ("to", toJson (hex (bytes target 20))),
    ("status", toJson ("0x1" : String)), ("logs", Json.arr #[log])]

private def indexed (sender : Nat) (tx : Rlp.Transaction1559)
    (hash : ByteArray) (wrongInput : Bool) : Json :=
  Json.mkObj [("hash", toJson (hex hash)),
    ("from", toJson (hex (bytes sender 20))),
    ("to", toJson (hex (bytes (tx.to.getD 0) 20))),
    ("chainId", toJson (quantity tx.chainId)), ("type", toJson ("0x2" : String)),
    ("nonce", toJson (quantity tx.nonce)), ("value", toJson (quantity tx.value)),
    ("gas", toJson (quantity tx.gas)),
    ("maxFeePerGas", toJson (quantity tx.maxFeePerGas)),
    ("maxPriorityFeePerGas", toJson (quantity tx.maxPriorityFeePerGas)),
    ("input", toJson (hex (if wrongInput then ByteArray.empty else tx.data))),
    ("blockHash", toJson (hex (bytes 17 32))),
    ("blockNumber", toJson ("0x1" : String)),
    ("transactionIndex", toJson ("0x0" : String))]

inductive Fault where
  | none | preparedWrite | send | hash | event | indexed | finality
  | changedKey | pendingNonce | chain | highFee | postApprovalNonce
  | zeroGas | excessiveGas
  deriving BEq

private def testJournalPath := "/synthetic/deposit-journal.json"
private def testSenderLock := "/synthetic/.tornado-sender.lock"

private def scenario (items : Array DepositMulti.Item) (readings : DepositMulti.Readings)
    (key : ByteArray) (sender : Nat) (fault : Fault)
    (feeBase : Option Nat := none) (priorityFee : Nat := 1)
    (bounds : ProtectedTxSender.Bounds := { maxGas := DepositSend.maxTransactionGas }) :
    IO (Bool × Nat × Nat × ByteArray × Option String) := do
  let journal ← IO.mkRef ByteArray.empty
  let sends ← IO.mkRef (0 : Nat)
  let signs ← IO.mkRef (0 : Nat)
  let approved ← IO.mkRef false
  let lastTx ← IO.mkRef (none : Option Rlp.Transaction1559)
  let lastHash ← IO.mkRef ByteArray.empty
  let effects : DepositMultiSend.Effects := {
    rpc := fun _ method params => do
      match method with
      | .chainId => return toJson (if fault == .chain then "0x2" else "0x1")
      | .getTransactionCount =>
        let current ← sends.get
        if fault == .postApprovalNonce && (← approved.get) then
          return toJson (quantity (current + 1))
        if fault == .pendingNonce && params[1]? == some (toJson ("pending" : String)) then
          return toJson (quantity (current + 1))
        return toJson (quantity current)
      | .estimateGas => return toJson (quantity (if fault == .zeroGas then 0
          else if fault == .excessiveGas then 1666667 else 1156615))
      | .feeHistory =>
        let base := feeBase.getD (if fault == .highFee then 10000000000 else 1)
        return Json.mkObj [
          ("baseFeePerGas", toJson (#[quantity base, quantity base])),
          ("reward", toJson (#[#[quantity priorityFee]]))]
      | .getBalance => return toJson ("0xde0b6b3a7640000" : String)
      | .call => return toJson (hex (bytes items[0]!.pool.amount 32))
      | .sendRawTransaction =>
        require (!(← journal.get).isEmpty) "Broadcast lacked a durable journal."
        let parsed ← checked <| Json.parse ((String.fromUTF8? (← journal.get)).getD "")
        let rows ← checked <| (← checked <| parsed.getObjVal? "steps").getArr?
        let row := rows[(← sends.get)]!
        require ((← checked <| (← checked <| row.getObjVal? "status").getStr?) == "prepared")
          "Broadcast occurred before prepared state."
        let raw ← checked <| parseHexBytes (← checked <| params[0]!.getStr?)
        let hash := keccak256 raw
        lastHash.set hash
        sends.modify (· + 1)
        if fault == .send then throw <| IO.userError "transport disconnected"
        return toJson (hex (if fault == .hash then bytes 99 32 else hash))
      | .getTransactionReceipt =>
        let some tx ← lastTx.get | throw <| IO.userError "No signed test transaction."
        return receipt sender tx (← lastHash.get) (fault == .event)
      | .getTransactionByHash =>
        let some tx ← lastTx.get | throw <| IO.userError "No signed test transaction."
        return indexed sender tx (← lastHash.get) (fault == .indexed)
      | _ => throw <| IO.userError "Unexpected test RPC method.",
    createJournal := fun value => do
      require (← journal.get).isEmpty "Journal was overwritten."
      journal.set value,
    replaceJournal := fun old next => do
      require ((← journal.get) == old) "Journal compare-and-replace lost prior bytes."
      if fault == .preparedWrite then throw <| IO.userError "injected journal failure"
      journal.set next,
    sign := fun tx => do
      signs.modify (· + 1)
      require (← approved.get) "Signing occurred before approval."
      require (tx.gas == 1387939)
        "Signed transaction did not retain the buffered deposit gas estimate."
      require (tx.maxFeePerGas == 2 * feeBase.getD
        (if fault == .highFee then 10000000000 else 1) + priorityFee)
        "Signed transaction changed the reviewed maximum fee quote."
      let signed ← checked <| TypedTransaction.sign1559 tx key
      lastTx.set (some tx)
      return (if fault == .changedKey then sender + 1 else sender, signed),
    approve := fun _ => approved.set true,
    waitFinality := fun _ => do
      if fault == .finality then throw <| IO.userError "injected finality failure" }
  let failure : Option String ← try
    let _ ← DepositMultiSend.withFailureContext testJournalPath testSenderLock <|
      DepositMultiSend.executeWith effects items .mainnet sender readings bounds
    pure none
  catch error => pure (some error.toString)
  return (failure.isNone, ← sends.get, ← signs.get, ← journal.get, failure)

def main : IO UInt32 := do
  let key := bytes 1 32
  let publicAddress ← checked <| secp256k1EthereumAddress key
  let sender := publicAddress.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let some pool := poolFor .mainnet "0.01" "ETH"
    | throw <| IO.userError "Missing pinned test pool."
  let poolBytes ← checked <| parseHexBytes pool.address
  let poolAddress := poolBytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let items : Array DepositMulti.Item := #[⟨pool, bytes 1 32⟩, ⟨pool, bytes 2 32⟩]
  let readings : DepositMulti.Readings :=
    ⟨1, ByteArray.empty, 1000000000000000000, 0, #[⟨poolAddress, pool.amount, 0⟩]⟩
  let defaults : ProtectedTxSender.Bounds := { maxGas := DepositSend.maxTransactionGas }
  let smallBounds := DepositSend.stepBounds defaults pool.amount
  let customBounds := DepositSend.stepBounds
    { defaults with valueGasDivisor := 20, maxGasCostWei := 5000000000000000 }
    pool.amount
  require (smallBounds.valueGasDivisor == 0 &&
    smallBounds.maxGasCostWei == 20000000000000000 &&
    (DepositSend.stepBounds defaults 0).valueGasDivisor == 10 &&
    customBounds.valueGasDivisor == 20 &&
    customBounds.maxGasCostWei == 5000000000000000)
    "Small deposit exception widened approval or custom gas-cost bounds."
  let (success, sends, signs, journal, _) ← scenario items readings key sender .none
  require (success && sends == 2 && signs == 2)
    "Two exact sequential deposits did not complete."
  let journalText := (String.fromUTF8? journal).getD ""
  let parsed ← checked <| DepositStatus.parseJournal journalText
  require (parsed.steps.size == 2 && parsed.steps.all (·.status == .confirmed))
    "Multi-deposit journal is incompatible with status reconciliation."
  let (observed, observedSends, observedSigns, _, _) ←
    scenario items readings key sender .none (some 0) 1000000000
  require (1387939 * 1000000000 > pool.amount / 10 &&
    observed && observedSends == 2 && observedSigns == 2)
    "Observed 0.01 ETH 1 gwei fee was blocked by the old 10% sequential cap."
  let (customRelative, relativeSends, relativeSigns, _, relativeFailure) ←
    scenario items readings key sender .none (some 0) 1000000000
      { defaults with valueGasDivisor := 20 }
  require (!customRelative && relativeSends == 0 && relativeSigns == 0 &&
    reportedBound relativeFailure (pool.amount / 20))
    "Custom stricter relative gas-cost bound was weakened for small deposits."
  let (customAbsolute, absoluteSends, absoluteSigns, _, customAbsoluteFailure) ←
    scenario items readings key sender .none (some 0) 1000000000
      { defaults with maxGasCostWei := 1000000000000000 }
  require (!customAbsolute && absoluteSends == 0 && absoluteSigns == 0 &&
    reportedBound customAbsoluteFailure 1000000000000000)
    "Custom lower absolute gas-cost bound was weakened for small deposits."
  let some largerPool := poolFor .mainnet "0.1" "ETH"
    | throw <| IO.userError "Missing larger ETH fixture pool."
  let largerPoolBytes ← checked <| parseHexBytes largerPool.address
  let largerAddress := largerPoolBytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let largerItems : Array DepositMulti.Item := #[⟨largerPool, bytes 3 32⟩]
  let largerReadings : DepositMulti.Readings :=
    ⟨1, ByteArray.empty, 1000000000000000000, 0,
      #[⟨largerAddress, largerPool.amount, 0⟩]⟩
  let (relativeAccepted, largerSends, largerSigns, _, largerFailure) ←
    scenario largerItems largerReadings key sender .none (some 5000000000) 1000000000
  require ((DepositSend.stepBounds defaults largerPool.amount).valueGasDivisor == 10 &&
    1387939 * 11000000000 > largerPool.amount / 10 &&
    1387939 * 11000000000 < 20000000000000000 &&
    !relativeAccepted && largerSends == 0 && largerSigns == 0 &&
    reportedBound largerFailure (largerPool.amount / 10))
    "Deposit above 0.01 ETH bypassed the retained 10% sequential fee cap."
  let (overAbsolute, overAbsoluteSends, overAbsoluteSigns, _, absoluteFailure) ←
    scenario items readings key sender .none (some 7000000000) 1000000000
  require (1387939 * 15000000000 > 20000000000000000 &&
    !overAbsolute && overAbsoluteSends == 0 && overAbsoluteSigns == 0 &&
    reportedBound absoluteFailure 20000000000000000)
    "Small deposit bypassed the retained 0.02 ETH absolute fee cap."
  for fault in [Fault.preparedWrite, .changedKey, .pendingNonce, .chain,
      .highFee, .postApprovalNonce] do
    let (accepted, sent, _, _, _) ← scenario items readings key sender fault
    require (!accepted && sent == 0) "An invalid pre-exposure state broadcast a transaction."
  for fault in [Fault.zeroGas, .excessiveGas] do
    let (accepted, sent, signed, saved, _) ← scenario items readings key sender fault
    let recovered ← checked <| DepositStatus.parseJournal ((String.fromUTF8? saved).getD "")
    require (!accepted && sent == 0 && signed == 0 &&
      recovered.steps.all (fun step => step.status == .planned && step.hash.isNone))
      "A zero or excessive buffered gas estimate reached signing or broadcast."
  for (fault, expectedError, expectedSigns) in [
      (Fault.pendingNonce, "Sender has a pending transaction; refusing replacement.", 0),
      (Fault.preparedWrite, "injected journal failure", 1)] do
    let (accepted, sent, signed, saved, failure) ← scenario items readings key sender fault
    let some message := failure
      | throw <| IO.userError "A failed sequence discarded its original error."
    let warning := s!"Deposit sequence stopped. Inspect {testJournalPath}; sender lock remains at {testSenderLock}. Do not clear the lock or retry until every recorded hash is reconciled. For sequential ETH deposits, rerun the same command and original journal with --resume."
    let recovered ← checked <| DepositStatus.parseJournal ((String.fromUTF8? saved).getD "")
    require (!accepted && sent == 0 && signed == expectedSigns &&
      (message.splitOn expectedError).length > 1 && (message.splitOn warning).length > 1 &&
      recovered.steps.all (fun step => step.status == .planned && step.hash.isNone))
      "A pre-exposure failure lost its cause, lock warning, or unexposed journal state."
  for fault in [Fault.send, .hash, .event, .indexed, .finality] do
    let (accepted, sent, signed, saved, _) ← scenario items readings key sender fault
    require (!accepted && sent == 1 && signed == 1)
      "An ambiguous or mismatched result advanced to a second deposit."
    let savedText := (String.fromUTF8? saved).getD ""
    let recovered ← checked <| DepositStatus.parseJournal savedText
    require (recovered.steps[0]!.status == .unknown &&
      recovered.steps[0]!.hash.isSome && recovered.steps[1]!.status == .planned)
      "Unknown outcome lost its hash or changed the next planned deposit."
  IO.println "PASS: native multi-deposit sequence, durable-before-send, exact transaction/event binding, and ambiguity stop"
  return 0
