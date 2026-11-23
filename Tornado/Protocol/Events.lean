import Tornado.Crypto.Keccak

/-!
Strict ABI decoding of the three event shapes the pinned Tornado CLI uses to
reconcile deposits and ERC-4337 withdrawals. This is pure byte processing:
it does not authenticate RPC responses, prove finality, or query chain state.
-/

namespace Tornado.Protocol.Events

open Tornado.Crypto

structure Log where
  address : Nat
  topics : Array ByteArray
  data : ByteArray
  deriving Inhabited

structure Deposit where
  commitment : ByteArray
  leafIndex : Nat
  timestamp : Nat
  deriving Inhabited

structure Withdrawal where
  recipient : Nat
  nullifierHash : ByteArray
  relayer : Nat
  fee : Nat
  deriving Inhabited

structure UserOperationEvent where
  userOpHash : ByteArray
  sender : Nat
  paymaster : Nat
  nonce : Nat
  success : Bool
  actualGasCost : Nat
  actualGasUsed : Nat
  deriving Inhabited

def depositTopic : ByteArray :=
  keccak256 "Deposit(bytes32,uint32,uint256)".toUTF8

def withdrawalTopic : ByteArray :=
  keccak256 "Withdrawal(address,bytes32,address,uint256)".toUTF8

def userOperationTopic : ByteArray :=
  keccak256 "UserOperationEvent(bytes32,address,address,uint256,bool,uint256,uint256)".toUTF8

private def bytesNatBE (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def exactWord (bytes : ByteArray) (offset : Nat) : Except String ByteArray := do
  if offset + 32 > bytes.size then throw "Event data is truncated."
  return bytes.extract offset (offset + 32)

private def addressWord (word : ByteArray) : Except String Nat := do
  if word.size != 32 then throw "Event address word is truncated."
  let address := bytesNatBE word
  if address >= 2 ^ 160 then throw "Event address has nonzero ABI padding."
  return address

private def eventShape (log : Log) (topic : ByteArray)
    (topicCount dataBytes : Nat) : Except String Unit := do
  if log.address >= 2 ^ 160 || log.topics.size != topicCount ||
      log.data.size != dataBytes || log.topics[0]? != some topic ||
      log.topics.any (fun item => item.size != 32) then
    throw "Unrelated or malformed event log."

/-- Classic pool Deposit: one indexed commitment and two static data words. -/
def decodeDeposit (log : Log) : Except String Deposit := do
  eventShape log depositTopic 2 64
  let leafIndex := bytesNatBE (← exactWord log.data 0)
  if leafIndex >= 2 ^ 32 then throw "Deposit leafIndex is outside uint32."
  return { commitment := log.topics[1]!, leafIndex, timestamp := bytesNatBE (← exactWord log.data 32) }

/-- Classic pool Withdrawal: indexed relayer, three static data words. -/
def decodeWithdrawal (log : Log) : Except String Withdrawal := do
  eventShape log withdrawalTopic 2 96
  return { recipient := (← addressWord (← exactWord log.data 0)), nullifierHash := (← exactWord log.data 32), relayer := (← addressWord log.topics[1]!), fee := bytesNatBE (← exactWord log.data 64) }

/-- EntryPoint v0.8 UserOperationEvent: three indexed fields, four data words.
    Boolean values other than canonical zero or one are rejected. -/
def decodeUserOperationEvent (log : Log) : Except String UserOperationEvent := do
  eventShape log userOperationTopic 4 128
  let rawSuccess := bytesNatBE (← exactWord log.data 32)
  if rawSuccess > 1 then throw "UserOperationEvent success is not canonical bool."
  return { userOpHash := log.topics[1]!, sender := (← addressWord log.topics[2]!), paymaster := (← addressWord log.topics[3]!), nonce := bytesNatBE (← exactWord log.data 0), success := rawSuccess == 1, actualGasCost := bytesNatBE (← exactWord log.data 64), actualGasUsed := bytesNatBE (← exactWord log.data 96) }

structure ExpectedEntry where
  entryPoint : Nat
  userOpHash : ByteArray
  sender : Nat
  paymaster : Nat
  nonce : Nat
  deriving Inhabited

structure ExpectedWithdrawal where
  pool : Nat
  recipient : Nat
  nullifierHash : ByteArray
  relayer : Nat
  fee : Nat
  deriving Inhabited

structure ExpectedDeposit where
  pool : Nat
  commitment : ByteArray
  deriving Inhabited

def matchesDeposit (log : Log) (expected : ExpectedDeposit) : Bool :=
  if log.address != expected.pool then false
  else match decodeDeposit log with
    | .error _ => false
    | .ok event => event.commitment == expected.commitment

def matchesWithdrawal (log : Log) (expected : ExpectedWithdrawal) : Bool :=
  if log.address != expected.pool then false
  else match decodeWithdrawal log with
    | .error _ => false
    | .ok event =>
        event.recipient == expected.recipient &&
        event.nullifierHash == expected.nullifierHash &&
        event.relayer == expected.relayer && event.fee == expected.fee

/-- An accepted withdrawal match contains a decoded event with every
    caller-requested field equal, including the emitting pool address. -/
theorem matchesWithdrawal_sound (log : Log) (expected : ExpectedWithdrawal)
    (h : matchesWithdrawal log expected = true) :
    log.address = expected.pool ∧
      ∃ event, decodeWithdrawal log = .ok event ∧
        event.recipient = expected.recipient ∧
        (event.nullifierHash == expected.nullifierHash) = true ∧
        event.relayer = expected.relayer ∧ event.fee = expected.fee := by
  by_cases ha : log.address = expected.pool
  · cases hd : decodeWithdrawal log with
    | error _ => simp [matchesWithdrawal, ha, hd] at h
    | ok event =>
        simp [matchesWithdrawal, ha, hd, Bool.and_eq_true] at h
        exact ⟨ha, event, rfl, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
  · simp [matchesWithdrawal, ha] at h

private def matchingEntry (log : Log) (expected : ExpectedEntry) : Option Bool :=
  if log.address != expected.entryPoint then none
  else match decodeUserOperationEvent log with
    | .error _ => none
    | .ok event =>
        if event.userOpHash == expected.userOpHash &&
            event.sender == expected.sender &&
            event.paymaster == expected.paymaster &&
            event.nonce == expected.nonce then some event.success
        else none

/-- Multiple matching EntryPoint events are treated as ambiguous, even if
    a permissive decoder would accept the final occurrence. -/
def uniqueEntryResult (logs : List Log) (expected : ExpectedEntry) : Option Bool :=
  match logs.filterMap (matchingEntry · expected) with
  | [value] => some value
  | _ => none

def hasDeposit (logs : List Log) (expected : ExpectedDeposit) : Bool :=
  logs.any (matchesDeposit · expected)

def hasWithdrawal (logs : List Log) (expected : ExpectedWithdrawal) : Bool :=
  logs.any (matchesWithdrawal · expected)

inductive Outcome where
  | confirmed | failed | unknown
  deriving Repr, BEq, DecidableEq

/-- A sequential deposit confirms only with the exact pool and commitment
    event in a successful receipt. A reverted receipt is a definite failure. -/
def directDepositOutcome (receiptSuccess : Bool) (logs : List Log)
    (deposit : ExpectedDeposit) : Outcome :=
  if receiptSuccess && hasDeposit logs deposit then .confirmed
  else if !receiptSuccess then .failed
  else .unknown

private def distinctDeposits (expected : List ExpectedDeposit) : Bool :=
  let identities := expected.map (fun deposit => (deposit.pool, deposit.commitment))
  identities.eraseDups.length == identities.length

/-- The pinned CLI batch deposit path uses a zero-paymaster EntryPoint event
    and requires an exact Deposit event for every reviewed pool/commitment.
    Duplicate expected deposits and ambiguous EntryPoint logs cannot confirm. -/
def batchDepositOutcome (receiptSuccess : Bool) (logs : List Log)
    (entry : ExpectedEntry) (deposits : List ExpectedDeposit) : Outcome :=
  if receiptSuccess && entry.paymaster == 0 &&
      uniqueEntryResult logs entry == some true && !deposits.isEmpty &&
      distinctDeposits deposits && deposits.all (hasDeposit logs) then .confirmed
  else if !receiptSuccess || uniqueEntryResult logs entry == some false then .failed
  else .unknown

/-- Exact one-note receipt gate. The caller must independently establish that
    receipt status came from the selected chain and transaction hash. -/
def directOutcome (receiptSuccess : Bool) (logs : List Log)
    (entry : ExpectedEntry) (withdrawal : ExpectedWithdrawal) : Outcome :=
  if receiptSuccess && uniqueEntryResult logs entry == some true &&
      hasWithdrawal logs withdrawal then .confirmed
  else if receiptSuccess && uniqueEntryResult logs entry == some false then .failed
  else .unknown

private def distinctNullifiers (expected : List ExpectedWithdrawal) : Bool :=
  let values := expected.map (·.nullifierHash)
  values.eraseDups.length == values.length

/-- Every selected batch nullifier requires its own exact pool Withdrawal
    log. Duplicate expected nullifiers and ambiguous EntryPoint logs fail. -/
def batchOutcome (receiptSuccess : Bool) (logs : List Log)
    (entry : ExpectedEntry) (withdrawals : List ExpectedWithdrawal) : Outcome :=
  if receiptSuccess && uniqueEntryResult logs entry == some true &&
      !withdrawals.isEmpty && withdrawals.length <= 12 &&
      distinctNullifiers withdrawals &&
      withdrawals.all (hasWithdrawal logs) then .confirmed
  else if receiptSuccess && uniqueEntryResult logs entry == some false then .failed
  else .unknown

/-- A successful direct result requires the exact decoded EntryPoint and pool
    events, in addition to the caller-supplied receipt-success bit. -/
theorem direct_confirmation_requires_exact_events (receiptSuccess : Bool)
    (logs : List Log) (entry : ExpectedEntry) (withdrawal : ExpectedWithdrawal)
    (h : directOutcome receiptSuccess logs entry withdrawal = .confirmed) :
    receiptSuccess = true ∧ uniqueEntryResult logs entry = some true ∧
      hasWithdrawal logs withdrawal = true := by
  unfold directOutcome at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    exact ⟨guard.1.1, guard.1.2, guard.2⟩
  · split at h <;> contradiction

/-- The pure batch deposit checker cannot confirm without a successful
    receipt, zero-paymaster EntryPoint success, and every Deposit match. -/
theorem batch_deposit_confirmation_requires_all_events (receiptSuccess : Bool)
    (logs : List Log) (entry : ExpectedEntry) (deposits : List ExpectedDeposit)
    (h : batchDepositOutcome receiptSuccess logs entry deposits = .confirmed) :
    receiptSuccess = true ∧ entry.paymaster = 0 ∧
      uniqueEntryResult logs entry = some true ∧
      distinctDeposits deposits = true ∧
      deposits.all (hasDeposit logs) = true := by
  unfold batchDepositOutcome at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    exact ⟨guard.1.1.1.1.1, guard.1.1.1.1.2, guard.1.1.1.2,
      guard.1.2, guard.2⟩
  · split at h <;> contradiction

/-- A confirmed batch contains at least one selected, distinct nullifier and
    a matching decoded withdrawal log for every selected note. -/
theorem batch_confirmation_requires_all_events (receiptSuccess : Bool)
    (logs : List Log) (entry : ExpectedEntry)
    (withdrawals : List ExpectedWithdrawal)
    (h : batchOutcome receiptSuccess logs entry withdrawals = .confirmed) :
    receiptSuccess = true ∧ uniqueEntryResult logs entry = some true ∧
      distinctNullifiers withdrawals = true ∧
      withdrawals.all (hasWithdrawal logs) = true := by
  unfold batchOutcome at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    exact ⟨guard.1.1.1.1.1, guard.1.1.1.1.2, guard.1.2, guard.2⟩
  · split at h <;> contradiction

end Tornado.Protocol.Events

#print axioms Tornado.Protocol.Events.direct_confirmation_requires_exact_events
#print axioms Tornado.Protocol.Events.batch_confirmation_requires_all_events
#print axioms Tornado.Protocol.Events.matchesWithdrawal_sound
#print axioms Tornado.Protocol.Events.batch_deposit_confirmation_requires_all_events
