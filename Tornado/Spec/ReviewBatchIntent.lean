import Tornado.Cli.WithdrawalSend

/-! Semantic batch intent is inherited by the actual prepared CLI review.
The builder result is the same operation indexed by the runtime driver and
its signature-only payload certificate. These are local payload properties;
contract execution, filesystem durability and chain truth remain boundaries. -/

namespace Tornado.Spec.ReviewBatchIntent

open Tornado.Cli.WithdrawalSend Tornado.Protocol

theorem prepared_batch_decodes (review : Review) (prepared : PreparedReview review)
    (account : SponsoredWithdrawal.Account) (receiver : Nat)
    (calls : Array Abi.ContractCall)
    (mode : review.mode = .batch account receiver calls) :
    ∃ intent output,
      SponsoredWithdrawal.batchIntent review.notes account receiver calls review.gas = .ok intent ∧
      BatchWithdrawalIntent.decode intent prepared.operation = .ok output ∧
      BatchWithdrawalIntent.Matches intent prepared.operation output review.bounds := by
  have built := prepared.built
  unfold build at built
  rw [mode] at built
  simp only [bind, Except.bind, pure, Except.pure] at built
  split at built
  · contradiction
  ·
    split at built
    · contradiction
    ·
      exact SponsoredWithdrawal.batch_success_decodes review.notes account receiver calls
        review.gas review.bounds prepared.operation built

/-- The final authorized operation differs only by signature from the very
operation to which the prepared-review semantic theorem applies. -/
theorem finalized_preserves_prepared_batch (review : Review) (prepared : PreparedReview review)
    (payload : Tornado.Runtime.WithdrawalDriver.FinalPayload prepared.driver) :
    payload.operation = { prepared.operation with signature := payload.signed.signature } ∧
    payload.signed.owner = prepared.driver.owner :=
  ⟨payload.operationExact, payload.ownerBound⟩

end Tornado.Spec.ReviewBatchIntent

#print axioms Tornado.Spec.ReviewBatchIntent.prepared_batch_decodes
#print axioms Tornado.Spec.ReviewBatchIntent.finalized_preserves_prepared_batch
