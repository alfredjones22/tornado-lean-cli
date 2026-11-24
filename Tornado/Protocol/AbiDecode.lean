import Tornado.Protocol.Abi
import Tornado.SmartAccount.Recovery

/-!
Independent bounded readers for the ABI calls accepted by batch withdrawal
review. Fields are read from the supplied bytes before canonical re-encoding;
the decoder is never handed an expected call list or expected field values.
The final complete-byte comparison rejects alternate offsets, overlapping
tails, nonzero padding, and trailing bytes.
-/

namespace Tornado.Protocol.AbiDecode

open Tornado.Crypto

structure PoolWithdrawal where
  proof : ByteArray
  root : ByteArray
  nullifierHash : ByteArray
  recipient : Nat
  relayer : Nat
  fee : Nat
  refund : Nat
  deriving Inhabited, BEq

structure Transfer where
  recipient : Nat
  amount : Nat
  deriving Inhabited, BEq

structure FactoryCreate where
  owner : Nat
  salt : Nat
  deriving Inhabited, BEq

def maxBatchCalls : Nat := 24
def maxBatchDataBytes : Nat := 131072

/-- The largest supported canonical batch, including all ABI overhead and
up to 31 padding bytes for each call. This also bounds parsing work. -/
def maxBatchEncodedBytes : Nat := 4 + 64 + maxBatchCalls * (32 + 128 + 31) + maxBatchDataBytes

private def readBytes (bytes : ByteArray) (start count : Nat) : Except String ByteArray := do
  if start > bytes.size || count > bytes.size - start then
    throw "Truncated ABI data."
  return bytes.extract start (start + count)

private def readWord (bytes : ByteArray) (start : Nat) : Except String Nat := do
  let word ← readBytes bytes start 32
  return word.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def readAddress (bytes : ByteArray) (start : Nat) : Except String Nat := do
  let address ← readWord bytes start
  if address >= Abi.maxAddress then throw "ABI address is out of range."
  return address

private def requireSelector (bytes : ByteArray) (signature : String) : Except String Unit := do
  if (← readBytes bytes 0 4) != Abi.selector signature then
    throw "Unexpected ABI function selector."

private def readDynamicBytes (bytes : ByteArray) (start limit : Nat) : Except String ByteArray := do
  let size ← readWord bytes start
  if size > limit then throw "ABI dynamic bytes exceed the supported bound."
  readBytes bytes (start + 32) size

private def readBatchFields (bytes : ByteArray) : Except String (Array Abi.ContractCall) := do
  if bytes.size > maxBatchEncodedBytes then throw "ABI batch data exceed the supported bound."
  requireSelector bytes "executeBatch((address,uint256,bytes)[])"
  let arrayOffset ← readWord bytes 4
  let arrayStart := 4 + arrayOffset
  let count ← readWord bytes arrayStart
  if count == 0 || count > maxBatchCalls then throw "Unsupported ABI batch call count."
  let offsetsStart := arrayStart + 32
  let mut calls := #[]
  let mut total := 0
  for index in [0:count] do
    let offset ← readWord bytes (offsetsStart + 32 * index)
    let tupleStart := offsetsStart + offset
    let to ← readAddress bytes tupleStart
    let value ← readWord bytes (tupleStart + 32)
    let dataOffset ← readWord bytes (tupleStart + 64)
    let data ← readDynamicBytes bytes (tupleStart + dataOffset) Abi.maxCallBytes
    total := total + data.size
    if total > maxBatchDataBytes then throw "ABI batch total data exceed the supported bound."
    calls := calls.push { to, value, data }
  return calls

private def readWithdrawalFields (bytes : ByteArray) : Except String PoolWithdrawal := do
  if bytes.size > 4 + 224 + 32 + Abi.maxCallBytes + 31 then
    throw "ABI withdrawal data exceed the supported bound."
  requireSelector bytes "withdraw(bytes,bytes32,bytes32,address,address,uint256,uint256)"
  let offset ← readWord bytes 4
  let root ← readBytes bytes 36 32
  let nullifierHash ← readBytes bytes 68 32
  let recipient ← readAddress bytes 100
  let relayer ← readAddress bytes 132
  let fee ← readWord bytes 164
  let refund ← readWord bytes 196
  let proof ← readDynamicBytes bytes (4 + offset) Abi.maxCallBytes
  return { proof, root, nullifierHash, recipient, relayer, fee, refund }

private def readTransferFields (bytes : ByteArray) : Except String Transfer := do
  if bytes.size != 68 then throw "Unexpected ERC-20 transfer calldata length."
  requireSelector bytes "transfer(address,uint256)"
  let recipient ← readAddress bytes 4
  let amount ← readWord bytes 36
  return { recipient, amount }

private def readFactoryFields (bytes : ByteArray) : Except String FactoryCreate := do
  if bytes.size != 68 then throw "Unexpected factory calldata length."
  requireSelector bytes "createAccount(address,uint256)"
  let owner ← readAddress bytes 4
  let salt ← readWord bytes 36
  return { owner, salt }

def callShape (call : Abi.ContractCall) : Bool :=
  0 < call.to && call.to < Abi.maxAddress && call.value < Abi.maxUint256 &&
    call.data.size <= Abi.maxCallBytes

def batchShape (calls : Array Abi.ContractCall) : Prop :=
  0 < calls.size ∧ calls.size ≤ maxBatchCalls ∧ calls.all callShape = true ∧
    calls.foldl (fun total call => total + call.data.size) 0 ≤ maxBatchDataBytes

def withdrawalShape (data : PoolWithdrawal) : Prop :=
  data.proof.size ≤ Abi.maxCallBytes ∧ data.root.size = 32 ∧ data.nullifierHash.size = 32 ∧
    data.recipient < Abi.maxAddress ∧ data.relayer < Abi.maxAddress ∧
    data.fee < Abi.maxUint256 ∧ data.refund < Abi.maxUint256

def transferShape (data : Transfer) : Prop :=
  data.recipient < Abi.maxAddress ∧ data.amount < Abi.maxUint256

/-- This decoder supports the pinned withdrawal-account factory policy,
including its nonzero owner and exact deterministic salt. Both fields are
independently parsed before this check. -/
def factoryShape (data : FactoryCreate) : Prop :=
  0 < data.owner ∧ data.owner < Abi.maxAddress ∧
    data.salt = Tornado.SmartAccount.withdrawalAccountSalt

instance : DecidablePred batchShape := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
instance : DecidablePred withdrawalShape := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
instance : DecidablePred transferShape := fun _ => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred factoryShape := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def encodeWithdrawal (data : PoolWithdrawal) : Except String ByteArray :=
  Abi.poolWithdraw data.proof data.root data.nullifierHash data.recipient data.relayer data.fee data.refund

def encodeTransfer (data : Transfer) : Except String ByteArray :=
  Abi.erc20Transfer data.recipient data.amount

def encodeFactory (data : FactoryCreate) : Except String ByteArray :=
  Tornado.SmartAccount.accountFactoryData data.owner

private def strictDecode {α : Type} (parse : ByteArray → Except String α)
    (encode : α → Except String ByteArray) (shape : α → Prop) [DecidablePred shape]
    (bytes : ByteArray) : Except String α :=
  match parse bytes with
  | .error error => .error error
  | .ok fields =>
    if shape fields then
      match encode fields with
      | .error error => .error error
      | .ok encoded =>
        if encoded == bytes then .ok fields else .error "Noncanonical ABI calldata."
    else .error "Decoded ABI fields exceed the supported shape."

private theorem strictDecode_sound {α : Type} (parse : ByteArray → Except String α)
    (encode : α → Except String ByteArray) (shape : α → Prop) [DecidablePred shape]
    (bytes : ByteArray) (value : α)
    (h : strictDecode parse encode shape bytes = .ok value) :
    encode value = .ok bytes ∧ shape value := by
  cases hParse : parse bytes with
  | error error => simp [strictDecode, hParse] at h
  | ok fields =>
    by_cases hShape : shape fields
    · cases hEncode : encode fields with
      | error error => simp [strictDecode, hParse, hShape, hEncode] at h
      | ok encoded =>
        by_cases hEqual : encoded == bytes
        · simp [strictDecode, hParse, hShape, hEncode, hEqual] at h
          cases h
          have hExact : encoded = bytes := Abi.byteArray_eq_of_beq hEqual
          exact ⟨by simpa [hExact] using hEncode, hShape⟩
        · simp [strictDecode, hParse, hShape, hEncode, hEqual] at h
    · simp [strictDecode, hParse, hShape] at h

/-- Decode the complete composed account call, preserving its call order. -/
def decodeAccountExecuteBatch (bytes : ByteArray) : Except String (Array Abi.ContractCall) :=
  strictDecode readBatchFields Abi.accountExecuteBatchComposed batchShape bytes

def decodePoolWithdraw (bytes : ByteArray) : Except String PoolWithdrawal :=
  strictDecode readWithdrawalFields encodeWithdrawal withdrawalShape bytes

def decodeErc20Transfer (bytes : ByteArray) : Except String Transfer :=
  strictDecode readTransferFields encodeTransfer transferShape bytes

def decodeFactoryCreate (bytes : ByteArray) : Except String FactoryCreate :=
  strictDecode readFactoryFields encodeFactory factoryShape bytes

theorem decoded_batch_reencodes (bytes : ByteArray) (calls : Array Abi.ContractCall)
    (h : decodeAccountExecuteBatch bytes = .ok calls) :
    Abi.accountExecuteBatchComposed calls = .ok bytes :=
  (strictDecode_sound _ _ _ bytes calls h).1

theorem decoded_batch_shape (bytes : ByteArray) (calls : Array Abi.ContractCall)
    (h : decodeAccountExecuteBatch bytes = .ok calls) : batchShape calls :=
  (strictDecode_sound _ _ _ bytes calls h).2

theorem decoded_batch_count (bytes : ByteArray) (calls : Array Abi.ContractCall)
    (h : decodeAccountExecuteBatch bytes = .ok calls) :
    0 < calls.size ∧ calls.size ≤ maxBatchCalls :=
  ⟨(decoded_batch_shape bytes calls h).1, (decoded_batch_shape bytes calls h).2.1⟩

theorem decoded_batch_call_shape (bytes : ByteArray) (calls : Array Abi.ContractCall)
    (h : decodeAccountExecuteBatch bytes = .ok calls) (index : Nat) (hi : index < calls.size) :
    0 < calls[index].to ∧ calls[index].to < Abi.maxAddress ∧
      calls[index].value < Abi.maxUint256 ∧ calls[index].data.size ≤ Abi.maxCallBytes := by
  have hAll := (decoded_batch_shape bytes calls h).2.2.1
  have hCall := (Array.all_eq_true.mp hAll) index hi
  simpa only [callShape, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using hCall

theorem decoded_batch_total_bytes (bytes : ByteArray) (calls : Array Abi.ContractCall)
    (h : decodeAccountExecuteBatch bytes = .ok calls) :
    calls.foldl (fun total call => total + call.data.size) 0 ≤ maxBatchDataBytes :=
  (decoded_batch_shape bytes calls h).2.2.2

theorem decoded_withdrawal_reencodes (bytes : ByteArray) (data : PoolWithdrawal)
    (h : decodePoolWithdraw bytes = .ok data) : encodeWithdrawal data = .ok bytes :=
  (strictDecode_sound _ _ _ bytes data h).1

theorem decoded_withdrawal_shape (bytes : ByteArray) (data : PoolWithdrawal)
    (h : decodePoolWithdraw bytes = .ok data) : withdrawalShape data :=
  (strictDecode_sound _ _ _ bytes data h).2

theorem decoded_transfer_reencodes (bytes : ByteArray) (data : Transfer)
    (h : decodeErc20Transfer bytes = .ok data) : encodeTransfer data = .ok bytes :=
  (strictDecode_sound _ _ _ bytes data h).1

theorem decoded_transfer_shape (bytes : ByteArray) (data : Transfer)
    (h : decodeErc20Transfer bytes = .ok data) : transferShape data :=
  (strictDecode_sound _ _ _ bytes data h).2

theorem decoded_factory_reencodes (bytes : ByteArray) (data : FactoryCreate)
    (h : decodeFactoryCreate bytes = .ok data) :
    Tornado.SmartAccount.accountFactoryData data.owner = .ok bytes :=
  (strictDecode_sound _ _ _ bytes data h).1

theorem decoded_factory_shape (bytes : ByteArray) (data : FactoryCreate)
    (h : decodeFactoryCreate bytes = .ok data) : factoryShape data :=
  (strictDecode_sound _ _ _ bytes data h).2

end Tornado.Protocol.AbiDecode

#print axioms Tornado.Protocol.AbiDecode.strictDecode_sound
#print axioms Tornado.Protocol.AbiDecode.decoded_batch_reencodes
#print axioms Tornado.Protocol.AbiDecode.decoded_batch_shape
#print axioms Tornado.Protocol.AbiDecode.decoded_batch_count
#print axioms Tornado.Protocol.AbiDecode.decoded_batch_call_shape
#print axioms Tornado.Protocol.AbiDecode.decoded_batch_total_bytes
#print axioms Tornado.Protocol.AbiDecode.decoded_withdrawal_reencodes
#print axioms Tornado.Protocol.AbiDecode.decoded_withdrawal_shape
#print axioms Tornado.Protocol.AbiDecode.decoded_transfer_reencodes
#print axioms Tornado.Protocol.AbiDecode.decoded_transfer_shape
#print axioms Tornado.Protocol.AbiDecode.decoded_factory_reencodes
#print axioms Tornado.Protocol.AbiDecode.decoded_factory_shape
