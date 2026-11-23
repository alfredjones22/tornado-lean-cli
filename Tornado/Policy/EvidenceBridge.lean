import Tornado.PolicyProofs
import Tornado.Policy.BatchProofs
import Tornado.Protocol.Events

/-!
Pure connection between strict event decoding and the one-note/batch policy
confirmation transitions. The caller still supplies the receipt status, logs,
expected fields and pre-confirmation state. This module does not authenticate
any of them against a chain or establish that the state is durably reachable.
-/

namespace Tornado.Policy.EvidenceBridge

open Tornado.Protocol.Events

def hashText (bytes : ByteArray) : String :=
  "0x" ++ Tornado.Crypto.bytesToHex bytes

def withdrawalTexts (withdrawals : List ExpectedWithdrawal) : List String :=
  withdrawals.map (fun item => hashText item.nullifierHash)

def directEvidence (receiptSuccess : Bool) (logs : List Log)
    (entry : ExpectedEntry) (withdrawal : ExpectedWithdrawal) : ConfirmationEvidence :=
  { receiptSuccess,
    entryPointEventMatches := uniqueEntryResult logs entry == some true,
    withdrawalEventMatches := hasWithdrawal logs withdrawal }

/-- A one-note candidate is confirmed only after the strict event gate and
    canonical signed UserOperation hash agree with the policy state. -/
def confirmDirect (state : Attempt) (receiptSuccess : Bool) (logs : List Log)
    (entry : ExpectedEntry) (withdrawal : ExpectedWithdrawal) : Except String Attempt :=
  if directOutcome receiptSuccess logs entry withdrawal = .confirmed then
    if state.signedHash = some (hashText entry.userOpHash) then
      stepAttempt state (.confirm (directEvidence receiptSuccess logs entry withdrawal))
    else .error "Signed hash differs from the decoded UserOperation."
  else .error "Receipt does not contain exact one-note confirmation evidence."

/-- A bridge success implies both the strict decoded-event result and a
    successful transition through the original one-note policy function. -/
theorem confirmDirect_sound (state after : Attempt) (receiptSuccess : Bool)
    (logs : List Log) (entry : ExpectedEntry) (withdrawal : ExpectedWithdrawal)
    (h : confirmDirect state receiptSuccess logs entry withdrawal = .ok after) :
    directOutcome receiptSuccess logs entry withdrawal = .confirmed ∧
    state.signedHash = some (hashText entry.userOpHash) ∧
    stepAttempt state (.confirm (directEvidence receiptSuccess logs entry withdrawal)) = .ok after ∧
    receiptSuccess = true ∧ uniqueEntryResult logs entry = some true ∧
    hasWithdrawal logs withdrawal = true := by
  by_cases ho : directOutcome receiptSuccess logs entry withdrawal = .confirmed
  · by_cases hh : state.signedHash = some (hashText entry.userOpHash)
    · have hp : stepAttempt state (.confirm (directEvidence receiptSuccess logs entry withdrawal)) = .ok after := by
        simpa [confirmDirect, ho, hh] using h
      obtain ⟨hr, he, hw⟩ := direct_confirmation_requires_exact_events receiptSuccess logs entry withdrawal ho
      exact ⟨ho, hh, hp, hr, he, hw⟩
    · simp [confirmDirect, ho, hh] at h
  · simp [confirmDirect, ho] at h

def batchEvidence (receiptSuccess : Bool) (logs : List Log)
    (entry : ExpectedEntry) (withdrawals : List ExpectedWithdrawal) : Batch.Evidence :=
  { receiptSuccess,
    entryPointEventMatches := uniqueEntryResult logs entry == some true,
    userOpHash := hashText entry.userOpHash,
    matchedNullifiers := withdrawalTexts withdrawals }

/-- Match the policy's textual selection to exactly the expected decoded
    nullifier list before passing it into its confirmation transition. -/
def confirmBatch (state : Batch.Attempt) (receiptSuccess : Bool)
    (logs : List Log) (entry : ExpectedEntry)
    (withdrawals : List ExpectedWithdrawal) : Except String Batch.Attempt :=
  if batchOutcome receiptSuccess logs entry withdrawals = .confirmed then
    if state.selected = withdrawalTexts withdrawals then
      if state.signedHash = some (hashText entry.userOpHash) then
        Batch.step state (.confirm (batchEvidence receiptSuccess logs entry withdrawals))
      else .error "Signed hash differs from the decoded UserOperation."
    else .error "Selected notes differ from the decoded withdrawal list."
  else .error "Receipt does not contain exact batch confirmation evidence."

/-- A bridge success is impossible without strict decoded evidence for every
    selected note and an accepted transition in the native batch policy. -/
theorem confirmBatch_sound (state after : Batch.Attempt) (receiptSuccess : Bool)
    (logs : List Log) (entry : ExpectedEntry)
    (withdrawals : List ExpectedWithdrawal)
    (h : confirmBatch state receiptSuccess logs entry withdrawals = .ok after) :
    batchOutcome receiptSuccess logs entry withdrawals = .confirmed ∧
    state.selected = withdrawalTexts withdrawals ∧
    state.signedHash = some (hashText entry.userOpHash) ∧
    Batch.step state (.confirm (batchEvidence receiptSuccess logs entry withdrawals)) = .ok after ∧
    receiptSuccess = true ∧ uniqueEntryResult logs entry = some true ∧
    withdrawals.all (hasWithdrawal logs) = true := by
  by_cases ho : batchOutcome receiptSuccess logs entry withdrawals = .confirmed
  · by_cases hs : state.selected = withdrawalTexts withdrawals
    · by_cases hh : state.signedHash = some (hashText entry.userOpHash)
      · have hp : Batch.step state (.confirm (batchEvidence receiptSuccess logs entry withdrawals)) = .ok after := by
          simpa [confirmBatch, ho, hs, hh] using h
        obtain ⟨hr, he, _, hw⟩ := batch_confirmation_requires_all_events receiptSuccess logs entry withdrawals ho
        exact ⟨ho, hs, hh, hp, hr, he, hw⟩
      · simp [confirmBatch, ho, hs, hh] at h
    · simp [confirmBatch, ho, hs] at h
  · simp [confirmBatch, ho] at h

end Tornado.Policy.EvidenceBridge

#print axioms Tornado.Policy.EvidenceBridge.confirmDirect_sound
#print axioms Tornado.Policy.EvidenceBridge.confirmBatch_sound
