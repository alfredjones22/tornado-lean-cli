import Lean
import Tornado.Domain.NoteIdentity
import Tornado.Protocol.Events
import Tornado.Runtime.JsonRpc

/-!
Pure parsing and reconciliation of the JSON-RPC receipt subset used by the
pinned Tornado CLI. These functions validate JSON shape and cross-field
consistency. They do not authenticate the HTTPS endpoint, verify Ethereum
consensus, bind a receipt to a chain ID, or establish finality.
-/

namespace Tornado.Protocol.RpcReceipt

open Lean Tornado.Domain Tornado.Protocol.Events

structure Receipt where
  transactionHash : ByteArray
  blockHash : ByteArray
  blockNumber : Nat
  transactionIndex : Nat
  origin : Nat
  to : Option Nat
  success : Bool
  logs : List Log
  deriving Inhabited

structure BundlerHint where
  userOpHash : ByteArray
  transactionHash : ByteArray
  entryPoint : Nat
  sender : Nat
  paymaster : Nat
  nonce : Nat
  success : Bool
  actualGasCost : Nat
  actualGasUsed : Nat
  deriving Inhabited

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def string (json : Json) (name : String) : Except String String := do
  (← field json name).getStr?

/-- EIP-1474 style quantity, rejecting uppercase digits, leading zeroes,
    empty values and values wider than uint256. -/
def quantity (raw : String) : Except String Nat :=
  Tornado.Runtime.JsonRpc.parseHexQuantity raw

private def quantityField (json : Json) (name : String) : Except String Nat :=
  (string json name).bind quantity

private def fixedHex (raw : String) (bytes : Nat) : Except String ByteArray := do
  if !raw.startsWith "0x" then throw "RPC data lacks 0x prefix."
  let result ← parseHexBytes raw
  if result.size != bytes then throw "RPC hex value has the wrong width."
  return result

private def bytesField (json : Json) (name : String) (width : Nat) : Except String ByteArray :=
  (string json name).bind (fixedHex · width)

private def addressField (json : Json) (name : String) : Except String Nat := do
  let bytes ← bytesField json name 20
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def dataField (json : Json) (name : String) : Except String ByteArray := do
  let raw ← string json name
  if !raw.startsWith "0x" then throw "RPC log data lacks 0x prefix."
  let bytes ← parseHexBytes raw
  if bytes.size > 1024 * 1024 then throw "RPC log data exceeds one MiB."
  return bytes

private def checkOptionalRemoved (json : Json) : Except String Unit := do
  match json.getObjVal? "removed" with
  | .error _ => pure ()
  | .ok .null => pure ()
  | .ok (.bool false) => pure ()
  | .ok _ => throw "Removed or malformed log cannot confirm an operation."

private def parseLog (json : Json) (transactionHash blockHash : ByteArray)
    (blockNumber transactionIndex : Nat) : Except String (Log × Nat) := do
  checkOptionalRemoved json
  let logHash ← bytesField json "transactionHash" 32
  let logBlockHash ← bytesField json "blockHash" 32
  let logBlockNumber ← quantityField json "blockNumber"
  let logTransactionIndex ← quantityField json "transactionIndex"
  if logHash != transactionHash || logBlockHash != blockHash ||
      logBlockNumber != blockNumber || logTransactionIndex != transactionIndex then
    throw "RPC log metadata differs from its receipt."
  let logIndex ← quantityField json "logIndex"
  let address ← addressField json "address"
  let topicValues ← (← field json "topics").getArr?
  if topicValues.size > 4 then throw "EVM log has more than four topics."
  let mut topics := #[]
  for item in topicValues do
    topics := topics.push (← fixedHex (← item.getStr?) 32)
  let data ← dataField json "data"
  return (⟨address, topics, data⟩, logIndex)

/-- Parse the exact chain-facing fields needed for receipt reconciliation.
    Every log must share the receipt's transaction and block identity. -/
def parseReceipt (json : Json) (expectedHash : ByteArray) : Except String Receipt := do
  if expectedHash.size != 32 then throw "Expected transaction hash is not bytes32."
  let transactionHash ← bytesField json "transactionHash" 32
  if transactionHash != expectedHash then throw "RPC receipt transaction hash differs from request."
  let blockHash ← bytesField json "blockHash" 32
  let blockNumber ← quantityField json "blockNumber"
  let transactionIndex ← quantityField json "transactionIndex"
  let origin ← addressField json "from"
  let to ← match (← field json "to") with
    | .null => pure none
    | .str address =>
      let bytes ← fixedHex address 20
      pure (some (bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0))
    | _ => throw "RPC recipient is neither an address nor null."
  let rawStatus ← string json "status"
  let success ← match rawStatus with
    | "0x1" => pure true
    | "0x0" => pure false
    | _ => throw "RPC receipt status must be 0x0 or 0x1."
  let rawLogs ← (← field json "logs").getArr?
  if rawLogs.size > 4096 then throw "RPC receipt contains too many logs."
  let mut logs := #[]
  let mut previous : Option Nat := none
  for rawLog in rawLogs do
    let (log, index) ← parseLog rawLog transactionHash blockHash blockNumber transactionIndex
    if previous.any (· >= index) then throw "RPC receipt log indexes are not strictly increasing."
    previous := some index
    logs := logs.push log
  return ⟨transactionHash, blockHash, blockNumber, transactionIndex,
    origin, to, success, logs.toList⟩

private def responseResult (root : Json) (expectedId : Nat) : Except String Json :=
  Tornado.Runtime.JsonRpc.decodeResult expectedId root

/-- `null` means no receipt yet. A present receipt must match the requested
    transaction hash, not merely contain a plausible event log. -/
def parseChainResponse (root : Json) (expectedId : Nat)
    (expectedHash : ByteArray) : Except String (Option Receipt) := do
  let result ← responseResult root expectedId
  match result with
  | .null => return none
  | _ => return some (← parseReceipt result expectedHash)

/-- Parse the bundler's UserOperation receipt as a hint. Its nested transaction
    hash is never itself accepted as proof of execution; chain receipt/events
    are checked separately. -/
def parseBundlerResponse (root : Json) (expectedId : Nat)
    (entry : ExpectedEntry) : Except String (Option BundlerHint) := do
  let result ← responseResult root expectedId
  match result with
  | .null => return none
  | _ =>
    if (← bytesField result "userOpHash" 32) != entry.userOpHash ||
        (← addressField result "entryPoint") != entry.entryPoint ||
        (← addressField result "sender") != entry.sender ||
        (← quantityField result "nonce") != entry.nonce then
      throw "Bundler receipt differs from the selected UserOperation."
    let paymaster ← match result.getObjVal? "paymaster" with
      | .error _ => pure 0
      | .ok .null => pure 0
      | .ok (.str address) =>
        let bytes ← fixedHex address 20
        pure (bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0)
      | .ok _ => throw "Malformed bundler paymaster address."
    if paymaster != entry.paymaster then throw "Bundler paymaster differs from reviewed operation."
    let success ← (← field result "success").getBool?
    let actualGasCost ← quantityField result "actualGasCost"
    let actualGasUsed ← quantityField result "actualGasUsed"
    let nestedReceipt ← field result "receipt"
    let transactionHash ← bytesField nestedReceipt "transactionHash" 32
    return some ⟨entry.userOpHash, transactionHash, entry.entryPoint,
      entry.sender, paymaster, entry.nonce, success,
      actualGasCost, actualGasUsed⟩

private def hintAgrees (hint : Option BundlerHint) (expectedHash : ByteArray)
    (entry : ExpectedEntry) (outcome : Outcome) : Bool :=
  match hint with
  | none => true
  | some value =>
    value.transactionHash == expectedHash &&
    value.userOpHash == entry.userOpHash &&
    value.entryPoint == entry.entryPoint &&
    value.sender == entry.sender &&
    value.paymaster == entry.paymaster &&
    value.nonce == entry.nonce &&
    (match outcome with
      | .confirmed => value.success
      | .failed => !value.success
      | .unknown => true)

private def receiptAgrees (receipt : Receipt) (expectedHash : ByteArray)
    (expectedTo : Nat) : Bool :=
  receipt.transactionHash == expectedHash && receipt.to == some expectedTo

/-- Pure one-note gate over a chain receipt and optional bundler hint. -/
def directWithdrawalOutcome (receipt : Receipt) (expectedHash : ByteArray)
    (entry : ExpectedEntry) (withdrawal : ExpectedWithdrawal)
    (hint : Option BundlerHint) : Outcome :=
  let chain := Tornado.Protocol.Events.directOutcome receipt.success receipt.logs entry withdrawal
  if receiptAgrees receipt expectedHash entry.entryPoint &&
      hintAgrees hint expectedHash entry chain then chain else .unknown

def batchWithdrawalOutcome (receipt : Receipt) (expectedHash : ByteArray)
    (entry : ExpectedEntry) (withdrawals : List ExpectedWithdrawal)
    (hint : Option BundlerHint) : Outcome :=
  let chain := Tornado.Protocol.Events.batchOutcome receipt.success receipt.logs entry withdrawals
  if receiptAgrees receipt expectedHash entry.entryPoint &&
      hintAgrees hint expectedHash entry chain then chain else .unknown

def depositOutcome (receipt : Receipt) (expectedHash : ByteArray)
    (deposit : ExpectedDeposit) : Outcome :=
  if receiptAgrees receipt expectedHash deposit.pool then
    Tornado.Protocol.Events.directDepositOutcome receipt.success receipt.logs deposit
  else .unknown

/-- A relayer transaction calls the pool directly. A reverted outer receipt
    remains unknown here because a relayer's job status may require separate
    reconciliation before any retry is considered. -/
def relayerWithdrawalOutcome (receipt : Receipt) (expectedHash : ByteArray)
    (withdrawal : ExpectedWithdrawal) : Outcome :=
  if receiptAgrees receipt expectedHash withdrawal.pool &&
      receipt.success && hasWithdrawal receipt.logs withdrawal then
    .confirmed
  else .unknown

/-- A Simple7702 batch deposit is routed through EntryPoint and requires all
    selected pool Deposit events in the same exact transaction receipt. -/
def batchDepositOutcome (receipt : Receipt) (expectedHash : ByteArray)
    (entry : ExpectedEntry) (deposits : List ExpectedDeposit)
    (hint : Option BundlerHint) : Outcome :=
  let chain := Tornado.Protocol.Events.batchDepositOutcome receipt.success receipt.logs entry deposits
  if receiptAgrees receipt expectedHash entry.entryPoint &&
      hintAgrees hint expectedHash entry chain then chain else .unknown

/-- Confirmation cannot be reported for a different transaction hash or an
    unexpected EntryPoint transaction destination. -/
theorem direct_confirmation_binds_transaction (receipt : Receipt)
    (expectedHash : ByteArray) (entry : ExpectedEntry)
    (withdrawal : ExpectedWithdrawal) (hint : Option BundlerHint)
    (h : directWithdrawalOutcome receipt expectedHash entry withdrawal hint = .confirmed) :
    (receipt.transactionHash == expectedHash) = true ∧
    receipt.to = some entry.entryPoint ∧
    Tornado.Protocol.Events.directOutcome receipt.success receipt.logs entry withdrawal = .confirmed := by
  by_cases guard :
      (receiptAgrees receipt expectedHash entry.entryPoint &&
        hintAgrees hint expectedHash entry
          (Tornado.Protocol.Events.directOutcome receipt.success receipt.logs entry withdrawal)) = true
  · have chain : Tornado.Protocol.Events.directOutcome receipt.success receipt.logs entry withdrawal = .confirmed := by
      simpa [directWithdrawalOutcome, guard] using h
    simp only [Bool.and_eq_true] at guard
    have bound : receiptAgrees receipt expectedHash entry.entryPoint = true := guard.1
    simp only [receiptAgrees, Bool.and_eq_true] at bound
    exact ⟨bound.1, (beq_iff_eq).mp bound.2, chain⟩
  · simp [directWithdrawalOutcome, guard] at h

/-- The batch confirmation gate has the same transaction binding. -/
theorem batch_confirmation_binds_transaction (receipt : Receipt)
    (expectedHash : ByteArray) (entry : ExpectedEntry)
    (withdrawals : List ExpectedWithdrawal) (hint : Option BundlerHint)
    (h : batchWithdrawalOutcome receipt expectedHash entry withdrawals hint = .confirmed) :
    (receipt.transactionHash == expectedHash) = true ∧
    receipt.to = some entry.entryPoint ∧
    Tornado.Protocol.Events.batchOutcome receipt.success receipt.logs entry withdrawals = .confirmed := by
  by_cases guard :
      (receiptAgrees receipt expectedHash entry.entryPoint &&
        hintAgrees hint expectedHash entry
          (Tornado.Protocol.Events.batchOutcome receipt.success receipt.logs entry withdrawals)) = true
  · have chain : Tornado.Protocol.Events.batchOutcome receipt.success receipt.logs entry withdrawals = .confirmed := by
      simpa [batchWithdrawalOutcome, guard] using h
    simp only [Bool.and_eq_true] at guard
    have bound : receiptAgrees receipt expectedHash entry.entryPoint = true := guard.1
    simp only [receiptAgrees, Bool.and_eq_true] at bound
    exact ⟨bound.1, (beq_iff_eq).mp bound.2, chain⟩
  · simp [batchWithdrawalOutcome, guard] at h

/-- Batch deposit confirmation requires the exact EntryPoint destination,
    transaction hash and the event module's all-deposits confirmation gate. -/
theorem batch_deposit_confirmation_binds_transaction (receipt : Receipt)
    (expectedHash : ByteArray) (entry : ExpectedEntry)
    (deposits : List ExpectedDeposit) (hint : Option BundlerHint)
    (h : batchDepositOutcome receipt expectedHash entry deposits hint = .confirmed) :
    (receipt.transactionHash == expectedHash) = true ∧
    receipt.to = some entry.entryPoint ∧
    Tornado.Protocol.Events.batchDepositOutcome receipt.success receipt.logs entry deposits = .confirmed := by
  by_cases guard :
      (receiptAgrees receipt expectedHash entry.entryPoint &&
        hintAgrees hint expectedHash entry
          (Tornado.Protocol.Events.batchDepositOutcome receipt.success receipt.logs entry deposits)) = true
  · have chain : Tornado.Protocol.Events.batchDepositOutcome receipt.success receipt.logs entry deposits = .confirmed := by
      simpa [batchDepositOutcome, guard] using h
    simp only [Bool.and_eq_true] at guard
    have bound : receiptAgrees receipt expectedHash entry.entryPoint = true := guard.1
    simp only [receiptAgrees, Bool.and_eq_true] at bound
    exact ⟨bound.1, (beq_iff_eq).mp bound.2, chain⟩
  · simp [batchDepositOutcome, guard] at h

end Tornado.Protocol.RpcReceipt

#print axioms Tornado.Protocol.RpcReceipt.direct_confirmation_binds_transaction
#print axioms Tornado.Protocol.RpcReceipt.batch_confirmation_binds_transaction
#print axioms Tornado.Protocol.RpcReceipt.batch_deposit_confirmation_binds_transaction
