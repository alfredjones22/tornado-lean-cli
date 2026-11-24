import Tornado.Protocol.AbiDecode
import Tornado.Runtime.Bundler

/-! Independent field-level meaning of a sponsored smart-account batch. The
expected intent contains original request fields and catalog denominations,
not calldata produced by the builder. Decoding consumes the entire canonical
account, sponsor and deployment payloads before this gate accepts a result. -/

namespace Tornado.Protocol.BatchWithdrawalIntent

open Tornado.Protocol.UserOperation08

structure Withdrawal where
  pool : Nat
  proof : Array UInt8
  root : Nat
  nullifierHash : Nat
  recipient : Nat
  relayer : Nat
  fee : Nat
  refund : Nat
  deriving Inhabited, DecidableEq

structure Note where
  withdrawal : Withdrawal
  denomination : Nat
  deriving Inhabited

structure Call where
  to : Nat
  value : Nat
  data : Array UInt8
  deriving Inhabited, DecidableEq

def callFields (call : Abi.ContractCall) : Call :=
  ⟨call.to, call.value, call.data.data⟩

structure Intent where
  notes : Array Note
  account : Nat
  owner : Nat
  nonce : Nat
  deployed : Bool
  receiver : Nat
  sponsor : Nat
  token : Option Nat
  tail : Array Abi.ContractCall
  verificationGas : Nat
  executionGas : Nat
  preVerificationGas : Nat
  paymasterVerificationGas : Nat
  postOpGas : Nat
  maxFee : Nat
  priorityFee : Nat
  deriving Inhabited

private def bytesNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def withdrawalFields (target : Nat) (data : AbiDecode.PoolWithdrawal) : Withdrawal := {
  pool := target, proof := data.proof.data, root := bytesNat data.root,
  nullifierHash := bytesNat data.nullifierHash, recipient := data.recipient,
  relayer := data.relayer, fee := data.fee, refund := data.refund }

structure DecodedWithdrawal where
  value : Nat
  withdrawal : Withdrawal
  deriving Inhabited, DecidableEq

/-- The decoded prefix contains every nonsponsoring note, in call order. -/
def decodeWithdrawals (calls : Array Abi.ContractCall) : Except String (Array DecodedWithdrawal) :=
  calls.mapM fun call => do
    let data ← AbiDecode.decodePoolWithdraw call.data
    return { value := call.value, withdrawal := withdrawalFields call.to data }

structure Decoded where
  sponsor : Abi.SponsorData
  calls : Array Abi.ContractCall
  withdrawals : Array DecodedWithdrawal
  factory : Option AbiDecode.FactoryCreate
  forwarding : Option AbiDecode.Transfer

/-- Parsing does not construct or compare expected ABI encodings. Canonical
ABI decoders independently recover selectors, offsets, ordered calls and
fields. A later field check binds these results to the original input. -/
def decode (intent : Intent) (op : UserOperation) : Except String Decoded := do
  let sponsor ← Abi.decodeSponsorParameters op.paymasterData
  let calls ← AbiDecode.decodeAccountExecuteBatch op.callData
  let withdrawals ← decodeWithdrawals (calls.extract 0 (intent.notes.size - 1))
  let factory ← match op.factory with
    | none => pure none
    | some _ => some <$> AbiDecode.decodeFactoryCreate op.factoryData
  let forwarding ← if intent.tail.isEmpty && intent.receiver != intent.account then
      match intent.token with
      | none => pure none
      | some _ =>
        match calls[intent.notes.size - 1]? with
        | none => throw "Missing batch token forwarding call."
        | some call => some <$> AbiDecode.decodeErc20Transfer call.data
    else pure none
  return { sponsor, calls, withdrawals, factory, forwarding }

def total (intent : Intent) : Nat :=
  intent.notes.foldl (fun amount note => amount + note.denomination) 0

def net (intent : Intent) : Nat := total intent - intent.notes[0]!.withdrawal.fee

/-- Request restrictions are semantic values: only the sponsor may pay a
fee, every withdrawal reaches the account, and every refund is zero. -/
def RequestPolicy (intent : Intent) : Prop :=
  intent.notes.size > 0 ∧ intent.notes.size ≤ 12 ∧
  intent.tail.size ≤ 12 ∧
  (Abi.validateCalls intent.tail (some intent.account)).isOk = true ∧
  (intent.notes.size = 1 → intent.tail.isEmpty = false) ∧
  intent.notes[0]!.withdrawal.recipient = intent.account ∧
  intent.notes[0]!.withdrawal.relayer = intent.sponsor ∧
  intent.notes[0]!.withdrawal.refund = 0 ∧
  intent.notes[0]!.withdrawal.fee > 0 ∧
  intent.notes[0]!.withdrawal.fee < intent.notes[0]!.denomination ∧
  (intent.notes.toList.drop 1).all (fun note =>
    note.withdrawal.recipient == intent.account && note.withdrawal.relayer == 0 &&
      note.withdrawal.fee == 0 && note.withdrawal.refund == 0) = true ∧
  (intent.tail.isEmpty = false → intent.receiver = intent.account) ∧
  (intent.notes.map (·.withdrawal.nullifierHash)).toList.Nodup ∧
  intent.notes.all (fun note => decide (0 < note.denomination)) = true ∧
  0 < intent.account ∧ intent.account < Abi.maxAddress ∧
  0 < intent.owner ∧ intent.owner < Abi.maxAddress ∧
  0 < intent.receiver ∧ intent.receiver < Abi.maxAddress ∧
  0 < intent.sponsor ∧ intent.sponsor < Abi.maxAddress

instance (intent : Intent) : Decidable (RequestPolicy intent) := by
  unfold RequestPolicy
  infer_instance

def SponsorMatches (intent : Intent) (sponsor : Abi.SponsorData) : Prop :=
  sponsor.instanceAddress = intent.notes[0]!.withdrawal.pool ∧
  sponsor.proof.data = intent.notes[0]!.withdrawal.proof ∧
  bytesNat sponsor.root = intent.notes[0]!.withdrawal.root ∧
  bytesNat sponsor.nullifierHash = intent.notes[0]!.withdrawal.nullifierHash ∧
  sponsor.recipient = intent.account ∧
  sponsor.fee = intent.notes[0]!.withdrawal.fee

instance (intent : Intent) (sponsor : Abi.SponsorData) : Decidable (SponsorMatches intent sponsor) := by
  unfold SponsorMatches
  infer_instance

/-- The exact withdrawal prefix is followed by either the exact reviewed
user calls, a single net forwarding call, or no additional call. -/
def ExecutionMatches (intent : Intent) (decoded : Decoded) : Prop :=
  decoded.withdrawals = (intent.notes.extract 1 intent.notes.size).map
    (fun note => { value := 0, withdrawal := note.withdrawal }) ∧
  if intent.tail.isEmpty then
    if intent.receiver = intent.account then
      decoded.calls.size = intent.notes.size - 1 ∧ decoded.forwarding.isNone = true
    else
      decoded.calls.size = intent.notes.size ∧
      match intent.token with
      | none =>
        callFields decoded.calls[intent.notes.size - 1]! =
          ⟨intent.receiver, net intent, #[]⟩ ∧ decoded.forwarding.isNone = true
      | some token =>
        decoded.calls[intent.notes.size - 1]!.to = token ∧
        decoded.calls[intent.notes.size - 1]!.value = 0 ∧
        match decoded.forwarding with
        | none => False
        | some transfer => transfer.recipient = intent.receiver ∧ transfer.amount = net intent
  else
    (decoded.calls.extract (intent.notes.size - 1) decoded.calls.size).map callFields =
      intent.tail.map callFields ∧
    decoded.calls.size = intent.notes.size - 1 + intent.tail.size ∧
    decoded.forwarding.isNone = true

instance (intent : Intent) (decoded : Decoded) : Decidable (ExecutionMatches intent decoded) := by
  unfold ExecutionMatches
  cases intent.token <;> cases decoded.forwarding <;> infer_instance

def DeploymentMatches (intent : Intent) (op : UserOperation) (decoded : Decoded) : Prop :=
  if intent.deployed then
    op.factory.isNone = true ∧ op.factoryData.size = 0 ∧ decoded.factory.isNone = true
  else
    (match op.factory with
    | some (.address factory) => factory = 0x13e9ed32155810fdbd067d4522c492d6f68e5944
    | _ => False) ∧
    match decoded.factory with
    | none => False
    | some factory => factory.owner = intent.owner ∧
      factory.salt = Tornado.SmartAccount.withdrawalAccountSalt

instance (intent : Intent) (op : UserOperation) (decoded : Decoded) :
    Decidable (DeploymentMatches intent op decoded) := by
  unfold DeploymentMatches
  cases hFactory : op.factory with
  | none => cases decoded.factory <;> infer_instance
  | some factory =>
    cases factory <;> cases decoded.factory <;> infer_instance

def Matches (intent : Intent) (op : UserOperation) (decoded : Decoded)
    (bounds : Tornado.Runtime.Bundler.Bounds) : Prop :=
  RequestPolicy intent ∧
  op.sender = intent.account ∧ op.nonce = intent.nonce ∧
  op.authorizationAddress.isNone = true ∧ op.paymaster = some intent.sponsor ∧
  op.paymasterSignature.isNone = true ∧ op.signature.size = 0 ∧
  op.verificationGasLimit = intent.verificationGas ∧ op.callGasLimit = intent.executionGas ∧
  op.preVerificationGas = intent.preVerificationGas ∧
  op.paymasterVerificationGasLimit = intent.paymasterVerificationGas ∧
  op.paymasterPostOpGasLimit = intent.postOpGas ∧
  op.maxFeePerGas = intent.maxFee ∧ op.maxPriorityFeePerGas = intent.priorityFee ∧
  intent.executionGas > 0 ∧
  (Tornado.Runtime.Bundler.validate op bounds).isOk = true ∧
  SponsorMatches intent decoded.sponsor ∧ ExecutionMatches intent decoded ∧
  DeploymentMatches intent op decoded

instance (intent : Intent) (op : UserOperation) (decoded : Decoded)
    (bounds : Tornado.Runtime.Bundler.Bounds) : Decidable (Matches intent op decoded bounds) := by
  unfold Matches
  infer_instance

structure Checked (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) where
  private mk ::
  output : Decoded
  decoded : decode intent op = .ok output
  agreement : Matches intent op output bounds

/-- Fail closed unless the complete independently decoded operation has the
original request, call order, denomination accounting and selected gas policy. -/
def accept (intent : Intent) (op : UserOperation) (bounds : Tornado.Runtime.Bundler.Bounds := {}) :
    Except String (Checked intent op bounds) :=
  match decoded : decode intent op with
  | .error _ => .error "Batch withdrawal calldata could not be decoded canonically."
  | .ok output =>
    if agreement : Matches intent op output bounds then
      .ok ⟨output, decoded, agreement⟩
    else .error "Encoded batch withdrawal differs from the reviewed intent."

theorem checked_complete_intent (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds) :
    ∃ output, decode intent op = .ok output ∧ Matches intent op output bounds :=
  ⟨checked.output, checked.decoded, checked.agreement⟩

theorem checked_request_policy (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds) :
    RequestPolicy intent := checked.agreement.1

theorem checked_semantics (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds) :
    SponsorMatches intent checked.output.sponsor ∧ ExecutionMatches intent checked.output ∧
      DeploymentMatches intent op checked.output := by
  rcases checked.agreement with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, sponsor, execution, deployment⟩
  exact ⟨sponsor, execution, deployment⟩

/-- The only paymaster tuple is the first selected note, paying its fee once.
User-authorized arbitrary tail calls retain their own contract semantics. -/
theorem checked_sponsor (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds) :
    SponsorMatches intent checked.output.sponsor :=
  (checked_semantics intent op bounds checked).1

theorem checked_payout (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds) :
    checked.output.sponsor.recipient = intent.account ∧
      checked.output.sponsor.fee = intent.notes[0]!.withdrawal.fee :=
  (checked_sponsor intent op bounds checked).2.2.2.2

/-- There is one generated call per remaining note, preserving every decoded
withdrawal field and order, with zero call value. RequestPolicy further fixes
every recipient, relayer, fee and refund. -/
theorem checked_withdrawal_order (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds) :
    checked.output.withdrawals = (intent.notes.extract 1 intent.notes.size).map
      (fun note => { value := 0, withdrawal := note.withdrawal }) :=
  (checked_semantics intent op bounds checked).2.1.1

theorem checked_exact_tail (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds)
    (tailPresent : intent.tail.isEmpty = false) :
    (checked.output.calls.extract (intent.notes.size - 1) checked.output.calls.size).map callFields =
      intent.tail.map callFields ∧
    checked.output.calls.size = intent.notes.size - 1 + intent.tail.size ∧
    checked.output.forwarding.isNone = true := by
  have suffix := (checked_semantics intent op bounds checked).2.1.2
  simpa [tailPresent] using suffix

/-- ETH forwarding is exactly sum of catalog denominations minus the sole
sponsor fee, with empty calldata and no additional calls after forwarding. -/
theorem checked_eth_net (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds)
    (noTail : intent.tail.isEmpty = true) (externalReceiver : intent.receiver ≠ intent.account)
    (eth : intent.token = none) :
    checked.output.calls.size = intent.notes.size ∧
    callFields checked.output.calls[intent.notes.size - 1]! =
      ⟨intent.receiver, total intent - intent.notes[0]!.withdrawal.fee, #[]⟩ := by
  have suffix := (checked_semantics intent op bounds checked).2.1.2
  simp only [noTail, ↓reduceIte, externalReceiver, eth, net] at suffix
  exact ⟨suffix.1, suffix.2.1⟩

/-- ERC-20 forwarding decodes to the exact receiver and net amount; the final
call targets the catalog token with zero ETH value and no extra suffix. -/
theorem checked_token_net (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds)
    (noTail : intent.tail.isEmpty = true) (externalReceiver : intent.receiver ≠ intent.account)
    (token : Nat) (erc20 : intent.token = some token) :
    checked.output.calls.size = intent.notes.size ∧
    checked.output.calls[intent.notes.size - 1]!.to = token ∧
    checked.output.calls[intent.notes.size - 1]!.value = 0 ∧
    ∃ transfer, checked.output.forwarding = some transfer ∧
      transfer.recipient = intent.receiver ∧
      transfer.amount = total intent - intent.notes[0]!.withdrawal.fee := by
  have suffix := (checked_semantics intent op bounds checked).2.1.2
  simp only [noTail, ↓reduceIte, externalReceiver, erc20, net] at suffix
  cases forwarding : checked.output.forwarding with
  | none => simp [forwarding] at suffix
  | some transfer =>
    simp only [forwarding] at suffix
    exact ⟨suffix.1, suffix.2.1, suffix.2.2.1, transfer, rfl,
      suffix.2.2.2.1, suffix.2.2.2.2⟩

theorem checked_account_and_deployment (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds) :
    op.sender = intent.account ∧ op.nonce = intent.nonce ∧
    op.authorizationAddress.isNone = true ∧ DeploymentMatches intent op checked.output := by
  rcases checked.agreement with
    ⟨_, sender, nonce, authorization, _, _, _, _, _, _, _, _, _, _, _, _, _, _, deployment⟩
  exact ⟨sender, nonce, authorization, deployment⟩

theorem checked_gas_policy (intent : Intent) (op : UserOperation)
    (bounds : Tornado.Runtime.Bundler.Bounds) (checked : Checked intent op bounds) :
    op.verificationGasLimit = intent.verificationGas ∧ op.callGasLimit = intent.executionGas ∧
    op.preVerificationGas = intent.preVerificationGas ∧
    op.paymasterVerificationGasLimit = intent.paymasterVerificationGas ∧
    op.paymasterPostOpGasLimit = intent.postOpGas ∧
    op.maxFeePerGas = intent.maxFee ∧ op.maxPriorityFeePerGas = intent.priorityFee ∧
    (Tornado.Runtime.Bundler.validate op bounds).isOk = true := by
  rcases checked.agreement with
    ⟨_, _, _, _, _, _, _, verification, execution, pre, paymasterVerification,
      post, maxFee, priority, _, bound, _, _, _⟩
  exact ⟨verification, execution, pre, paymasterVerification, post, maxFee, priority, bound⟩

end Tornado.Protocol.BatchWithdrawalIntent

#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_complete_intent
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_request_policy
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_semantics
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_sponsor
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_payout
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_withdrawal_order
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_exact_tail
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_eth_net
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_token_net
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_account_and_deployment
#print axioms Tornado.Protocol.BatchWithdrawalIntent.checked_gas_policy
