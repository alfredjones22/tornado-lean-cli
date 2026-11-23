import Tornado.Protocol.Abi
import Tornado.Protocol.UserOperation08

/-! Independent field-level requirements for a direct sponsored withdrawal.
The executable builder decodes its own sponsor calldata through this gate.
These properties concern encoded intent, not contract behavior or proof secrecy. -/

namespace Tornado.Protocol.DirectWithdrawalIntent

open Tornado.Protocol.UserOperation08

structure Intent where
  sender : Nat
  sponsor : Nat
  pool : Nat
  recipient : Nat
  proof : ByteArray
  root : ByteArray
  nullifierHash : ByteArray
  fee : Nat
  verificationGas : Nat
  preVerificationGas : Nat
  paymasterVerificationGas : Nat
  postOpGas : Nat
  maxFee : Nat
  priorityFee : Nat

/-- Exact semantic fields, independently of the operation hash. Byte arrays
are compared by their contents; no collision-resistance assumption is used. -/
def Matches (intent : Intent) (op : UserOperation) (decoded : Abi.SponsorData) : Prop :=
  op.sender = intent.sender ∧ op.nonce = 0 ∧
  op.factory.isNone = true ∧ op.factoryData.size = 0 ∧
  op.authorizationAddress.isNone = true ∧
  op.callData.size = 0 ∧ op.callGasLimit = 0 ∧
  op.paymaster = some intent.sponsor ∧ op.paymasterSignature.isNone = true ∧
  op.verificationGasLimit = intent.verificationGas ∧
  op.preVerificationGas = intent.preVerificationGas ∧
  op.paymasterVerificationGasLimit = intent.paymasterVerificationGas ∧
  op.paymasterPostOpGasLimit = intent.postOpGas ∧
  op.maxFeePerGas = intent.maxFee ∧ op.maxPriorityFeePerGas = intent.priorityFee ∧
  decoded.instanceAddress = intent.pool ∧ decoded.recipient = intent.recipient ∧
  decoded.fee = intent.fee ∧ decoded.proof.data = intent.proof.data ∧
  decoded.root.data = intent.root.data ∧ decoded.nullifierHash.data = intent.nullifierHash.data

instance (intent : Intent) (op : UserOperation) (decoded : Abi.SponsorData) :
    Decidable (Matches intent op decoded) := by
  unfold Matches
  infer_instance

structure Checked (intent : Intent) (op : UserOperation) where
  private mk ::
  sponsorData : Abi.SponsorData
  decoded : Abi.decodeSponsorParameters op.paymasterData = .ok sponsorData
  agreement : Matches intent op sponsorData

/-- A successful result carries the exact decoder result and all requirements.
Unexpected ABI fields, sender, gas policy or post-withdrawal actions fail closed. -/
def accept (intent : Intent) (op : UserOperation) : Except String (Checked intent op) :=
  match decoded : Abi.decodeSponsorParameters op.paymasterData with
  | .error _ => .error "Direct withdrawal sponsor data could not be decoded canonically."
  | .ok sponsorData =>
    if agreement : Matches intent op sponsorData then
      .ok ⟨sponsorData, decoded, agreement⟩
    else .error "Encoded direct withdrawal differs from the reviewed intent."

theorem checked_recipient (intent : Intent) (op : UserOperation)
    (checked : Checked intent op) : checked.sponsorData.recipient = intent.recipient :=
  checked.agreement.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem checked_payout (intent : Intent) (op : UserOperation)
    (checked : Checked intent op) :
    checked.sponsorData.instanceAddress = intent.pool ∧
    checked.sponsorData.recipient = intent.recipient ∧
    checked.sponsorData.fee = intent.fee := by
  have h := checked.agreement
  simp only [Matches] at h
  exact ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem checked_no_execution (intent : Intent) (op : UserOperation)
    (checked : Checked intent op) : op.callData.size = 0 ∧ op.callGasLimit = 0 :=
  ⟨checked.agreement.2.2.2.2.2.1, checked.agreement.2.2.2.2.2.2.1⟩

theorem checked_canonical_bytes (intent : Intent) (op : UserOperation)
    (checked : Checked intent op) :
    Abi.sponsorParameters checked.sponsorData = .ok op.paymasterData :=
  Abi.decoded_sponsor_reencodes op.paymasterData checked.sponsorData checked.decoded

theorem checked_complete_intent (intent : Intent) (op : UserOperation)
    (checked : Checked intent op) :
    ∃ decoded, Abi.decodeSponsorParameters op.paymasterData = .ok decoded ∧ Matches intent op decoded :=
  ⟨checked.sponsorData, checked.decoded, checked.agreement⟩

end Tornado.Protocol.DirectWithdrawalIntent

#print axioms Tornado.Protocol.DirectWithdrawalIntent.checked_recipient
#print axioms Tornado.Protocol.DirectWithdrawalIntent.checked_payout
#print axioms Tornado.Protocol.DirectWithdrawalIntent.checked_no_execution
#print axioms Tornado.Protocol.DirectWithdrawalIntent.checked_canonical_bytes
#print axioms Tornado.Protocol.DirectWithdrawalIntent.checked_complete_intent
