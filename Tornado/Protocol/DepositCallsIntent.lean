import Tornado.Protocol.DepositIntent
import Tornado.Protocol.AbiDecode
import Tornado.Protocol.UserOperation08

/-! Decoded correspondence between a certified deposit step sequence and
the account execution calldata used by Simple7702. Delegation authorization
has its own approval/exposure policy; this module does not imply that an
authorization is cryptographically limited to a particular operation. -/

namespace Tornado.Protocol.DepositCallsIntent

private def word (bytes : ByteArray) (offset : Nat) : Except String Nat := do
  if offset + 32 > bytes.size then throw "Truncated account execution word."
  return (bytes.extract offset (offset + 32)).data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def decodeSingle (bytes : ByteArray) : Except String Abi.ContractCall := do
  let target ← word bytes 4
  let value ← word bytes 36
  let offset ← word bytes 68
  let length ← word bytes (4 + offset)
  let start := 4 + offset + 32
  if target == 0 || target >= Abi.maxAddress || length > Abi.maxCallBytes ||
      start > bytes.size || length > bytes.size - start then
    throw "Invalid deposit account execution bounds."
  let data := bytes.extract start (start + length)
  let call : Abi.ContractCall := ⟨target, value, data⟩
  if (← Abi.accountExecute target value data) != bytes then
    throw "Noncanonical deposit account execution."
  return call

/-- One call uses execute; a composed sequence uses executeBatch. The reader
does not receive any expected target, value or calldata. -/
def decode (bytes : ByteArray) : Except String (Array Abi.ContractCall) := do
  if bytes.size > AbiDecode.maxBatchEncodedBytes then
    throw "Deposit account calldata exceeds its parsing limit."
  if bytes.extract 0 4 == Abi.selector "execute(address,uint256,bytes)" then
    return #[← decodeSingle bytes]
  AbiDecode.decodeAccountExecuteBatch bytes

def projected (steps : Array DepositIntent.EncodedStep)
    (calls : Array Abi.ContractCall) : Array DepositIntent.EncodedStep :=
  steps.mapIdx fun index step =>
    { step with to := calls[index]!.to, value := calls[index]!.value, data := calls[index]!.data }

structure Checked (steps : Array DepositIntent.EncodedStep) (bytes : ByteArray) where
  private mk ::
  calls : Array Abi.ContractCall
  parsed : decode bytes = .ok calls
  count : calls.size = steps.size
  nonempty : 0 < steps.size
  bounded : steps.size ≤ 15
  meaning : Array DepositIntent.Meaning
  reviewed : DepositIntent.decodeSteps steps = .ok meaning
  executable : DepositIntent.decodeSteps (projected steps calls) = .ok meaning

def accept (steps : Array DepositIntent.EncodedStep) (bytes : ByteArray) :
    Except String (Checked steps bytes) :=
  match parsed : decode bytes with
  | .error error => .error error
  | .ok calls =>
    if count : calls.size = steps.size then
      if nonempty : 0 < steps.size then
        if bounded : steps.size ≤ 15 then
          match reviewed : DepositIntent.decodeSteps steps with
          | .error error => .error error
          | .ok meaning =>
            match executable : DepositIntent.decodeSteps (projected steps calls) with
            | .error error => .error error
            | .ok actual =>
              if same : actual = meaning then
                .ok ⟨calls, parsed, count, nonempty, bounded, meaning, reviewed, same ▸ executable⟩
              else .error "Account execution differs from selected deposit steps."
        else .error "Too many deposit execution calls."
      else .error "Deposit execution is empty."
    else .error "Account execution changed the selected deposit step count."

theorem checked_decoded_steps (steps : Array DepositIntent.EncodedStep) (bytes : ByteArray)
    (checked : Checked steps bytes) :
    ∃ calls meaning, decode bytes = .ok calls ∧ calls.size = steps.size ∧
      DepositIntent.decodeSteps steps = .ok meaning ∧
      DepositIntent.decodeSteps (projected steps calls) = .ok meaning :=
  ⟨checked.calls, checked.meaning, checked.parsed, checked.count, checked.reviewed, checked.executable⟩

theorem checked_count (steps : Array DepositIntent.EncodedStep) (bytes : ByteArray)
    (checked : Checked steps bytes) : 0 < steps.size ∧ steps.size ≤ 15 :=
  ⟨checked.nonempty, checked.bounded⟩

/-- The final operation is checked directly, so gas refinement and signing
cannot bypass the exact account-call correspondence gate. -/
def acceptOperation (steps : Array DepositIntent.EncodedStep)
    (operation : UserOperation08.UserOperation) : Except String (Checked steps operation.callData) :=
  accept steps operation.callData

end Tornado.Protocol.DepositCallsIntent

#print axioms Tornado.Protocol.DepositCallsIntent.checked_decoded_steps
#print axioms Tornado.Protocol.DepositCallsIntent.checked_count
