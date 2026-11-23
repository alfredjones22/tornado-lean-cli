import Tornado.Crypto.Keccak

/-!
Native ABI subset used by the Tornado CLI's Classic pool, ERC-20, and
SimpleAccount calls. All values are canonical byte arrays or bounded natural
numbers. Encoding is pure Lean and never signs or submits a transaction.

This is deliberately a typed subset of Solidity ABI, not a general ABI parser.
It rejects out-of-range addresses and uint256 values before encoding.
-/

namespace Tornado.Protocol.Abi

open Tornado.Crypto

def maxUint256 : Nat := 2 ^ 256
def maxAddress : Nat := 2 ^ 160
def maxContractCalls : Nat := 12
def maxCallBytes : Nat := 16384
def maxTotalCallBytes : Nat := 65536

structure ContractCall where
  to : Nat
  value : Nat
  data : ByteArray
  deriving Inhabited, BEq

structure SponsorData where
  instanceAddress : Nat
  proof : ByteArray
  root : ByteArray
  nullifierHash : ByteArray
  recipient : Nat
  fee : Nat
  deriving Inhabited, BEq

private def natBytesBE (n count : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:count] do
    result := result.push ((n / 2 ^ (8 * (count - 1 - i)) % 256).toUInt8)
  return result

private def bytesNatBE (bytes : ByteArray) : Nat := Id.run do
  let mut result := 0
  for byte in bytes.data do
    result := result * 256 + byte.toNat
  return result

/-- Exact 32-byte big-endian uint256 word. -/
def uintWord (value : Nat) : Except String ByteArray := do
  if value >= maxUint256 then throw "ABI uint256 is out of range."
  return natBytesBE value 32

/-- ABI address word, including the required twelve leading zero bytes. -/
def addressWord (address : Nat) : Except String ByteArray := do
  if address >= maxAddress then throw "ABI address is out of range."
  return natBytesBE address 32

/-- Require a statically-sized `bytes32` value. -/
def bytes32Word (value : ByteArray) : Except String ByteArray := do
  if value.size != 32 then throw "ABI bytes32 requires exactly 32 bytes."
  return value

private def padRightToWord (bytes : ByteArray) : ByteArray := Id.run do
  let mut result := bytes
  for _ in [0:(32 - bytes.size % 32) % 32] do
    result := result.push 0
  return result

/-- Canonical length-prefixed, right-padded encoding of dynamic `bytes`. -/
def dynamicBytes (bytes : ByteArray) : Except String ByteArray := do
  return (← uintWord bytes.size) ++ padRightToWord bytes

/-- Four-byte selector derived from the exact Solidity signature. -/
def selector (signature : String) : ByteArray :=
  (keccak256 signature.toUTF8).extract 0 4

private def functionData (signature : String) (parameters : ByteArray) : ByteArray :=
  selector signature ++ parameters

/-- ERC-20 `approve(address,uint256)`. -/
def erc20Approve (spender amount : Nat) : Except String ByteArray := do
  return functionData "approve(address,uint256)" ((← addressWord spender) ++ (← uintWord amount))

/-- ERC-20 `transfer(address,uint256)`. -/
def erc20Transfer (recipient amount : Nat) : Except String ByteArray := do
  return functionData "transfer(address,uint256)" ((← addressWord recipient) ++ (← uintWord amount))

/-- Classic pool `deposit(bytes32)`. -/
def poolDeposit (commitment : ByteArray) : Except String ByteArray := do
  return functionData "deposit(bytes32)" (← bytes32Word commitment)

/-- Classic pool `withdraw(bytes,bytes32,bytes32,address,address,uint256,uint256)`.
    The dynamic proof begins after seven 32-byte head words. -/
def poolWithdraw (proof root nullifierHash : ByteArray) (recipient relayer fee refund : Nat) : Except String ByteArray := do
  let head := (← uintWord 224) ++ (← bytes32Word root) ++ (← bytes32Word nullifierHash) ++
    (← addressWord recipient) ++ (← addressWord relayer) ++ (← uintWord fee) ++ (← uintWord refund)
  return functionData "withdraw(bytes,bytes32,bytes32,address,address,uint256,uint256)"
    (head ++ (← dynamicBytes proof))

/-- SimpleAccount `execute(address,uint256,bytes)`. -/
def accountExecute (target value : Nat) (data : ByteArray) : Except String ByteArray := do
  let head := (← addressWord target) ++ (← uintWord value) ++ (← uintWord 96)
  return functionData "execute(address,uint256,bytes)" (head ++ (← dynamicBytes data))

/-- SimpleAccount `withdrawDepositTo(address,uint256)`. -/
def accountWithdrawDepositTo (recipient amount : Nat) : Except String ByteArray := do
  return functionData "withdrawDepositTo(address,uint256)"
    ((← addressWord recipient) ++ (← uintWord amount))

/-- Reject the same unsafe call shapes and byte limits as `canonicalCalls` in
    the TypeScript CLI. Address checksums and textual hex normalization happen
    before construction of this typed value. -/
def validateCalls (calls : Array ContractCall) (account : Option Nat := none) : Except String (Array ContractCall) := do
  if calls.size > maxContractCalls then throw s!"Use up to {maxContractCalls} contract calls."
  let mut total := 0
  for call in calls do
    if call.to == 0 || call.to >= maxAddress then throw "Invalid contract call target."
    if account == some call.to then throw "Calls to the smart account itself are disabled to protect recovery."
    if call.value >= maxUint256 then throw "Contract call value must be a uint256 amount of wei."
    total := total + call.data.size
    if call.data.size > maxCallBytes || total > maxTotalCallBytes then
      throw "Contract call data exceeds the 16 KiB per-call or 64 KiB total limit."
  return calls

private def encodeCallTuple (call : ContractCall) : Except String ByteArray := do
  return (← addressWord call.to) ++ (← uintWord call.value) ++ (← uintWord 96) ++
    (← dynamicBytes call.data)

/-- ABI parameter encoding for one `(address,uint256,bytes)[]` argument. Its
    32-byte top-level offset and the array's element offsets match viem. -/
private def encodeCallArrayParameters (calls : Array ContractCall) : Except String ByteArray := do
  let mut offsets := ByteArray.empty
  let mut elements := ByteArray.empty
  for call in calls do
    offsets := offsets ++ (← uintWord (32 * calls.size + elements.size))
    elements := elements ++ (← encodeCallTuple call)
  return (← uintWord 32) ++ (← uintWord calls.size) ++ offsets ++ elements

def callArrayParameters (calls : Array ContractCall) : Except String ByteArray := do
  let _ ← validateCalls calls
  encodeCallArrayParameters calls

/-- Hash used by `callsHash` to bind ordered, validated contract calls. -/
def callsHash (calls : Array ContractCall) : Except String ByteArray := do
  return keccak256 (← callArrayParameters calls)

/-- SimpleAccount `executeBatch((address,uint256,bytes)[])`. -/
def accountExecuteBatch (calls : Array ContractCall) : Except String ByteArray := do
  return functionData "executeBatch((address,uint256,bytes)[])" (← callArrayParameters calls)

/-- Composed account execution includes up to eleven internal withdrawal
calls plus twelve separately validated user calls. The user-action limit in
`validateCalls` remains twelve; this larger bound applies only after the
withdrawal builder has checked its internal calls. -/
def accountExecuteBatchComposed (calls : Array ContractCall) : Except String ByteArray := do
  if calls.isEmpty || calls.size > 24 then throw "Too many composed account calls."
  let mut total := 0
  for call in calls do
    total := total + call.data.size
    if call.to == 0 || call.to >= maxAddress || call.value >= maxUint256 ||
        call.data.size > maxCallBytes || total > 131072 then
      throw "Composed account calls exceed the supported bounds."
  return functionData "executeBatch((address,uint256,bytes)[])"
    (← encodeCallArrayParameters calls)

/-- Sponsor paymaster tuple parameters. The tuple itself is a dynamic ABI
    argument; its offset is 32 and the proof offset is six words. -/
def sponsorParameters (data : SponsorData) : Except String ByteArray := do
  let head := (← addressWord data.instanceAddress) ++ (← uintWord 192) ++
    (← bytes32Word data.root) ++ (← bytes32Word data.nullifierHash) ++
    (← addressWord data.recipient) ++ (← uintWord data.fee)
  return (← uintWord 32) ++ head ++ (← dynamicBytes data.proof)

private def slice (bytes : ByteArray) (start count : Nat) : Except String ByteArray := do
  if start > bytes.size || count > bytes.size - start then throw "Truncated ABI data."
  return bytes.extract start (start + count)

private def decodeWord (bytes : ByteArray) (start : Nat) : Except String Nat := do
  return bytesNatBE (← slice bytes start 32)

private def decodeAddress (bytes : ByteArray) (start : Nat) : Except String Nat := do
  let value ← decodeWord bytes start
  if value >= maxAddress then throw "ABI address is out of range."
  return value

private def decodeSponsorFields (bytes : ByteArray) : Except String SponsorData := do
  if (← decodeWord bytes 0) != 32 then throw "Unexpected sponsor tuple offset."
  let instanceAddress ← decodeAddress bytes 32
  if (← decodeWord bytes 64) != 192 then throw "Unexpected sponsor proof offset."
  let root ← slice bytes 96 32
  let nullifierHash ← slice bytes 128 32
  let recipient ← decodeAddress bytes 160
  let fee ← decodeWord bytes 192
  let proofLen ← decodeWord bytes 224
  if proofLen > bytes.size then throw "Truncated sponsor proof."
  let proof ← slice bytes 256 proofLen
  return { instanceAddress, proof, root, nullifierHash, recipient, fee }

private def acceptCanonicalSponsor (bytes : ByteArray) (data : SponsorData) : Except String SponsorData :=
  match sponsorParameters data with
  | .error error => .error error
  | .ok encoded =>
    if encoded == bytes then .ok data else .error "Noncanonical sponsor ABI data."

theorem byteArray_eq_of_beq {left right : ByteArray}
    (h : (left == right) = true) : left = right := by
  cases left with
  | mk leftData =>
    cases right with
    | mk rightData =>
      have hData : (leftData == rightData) = true := by simpa only [BEq.beq] using h
      have hEq : leftData = rightData := (beq_iff_eq).mp hData
      simp [hEq]

/-- Strict canonical decoder for the paymaster sponsor tuple used in batch
    review. Re-encoding rejects overlapping tails, wrong offsets, nonzero
    padding, and trailing data. This is narrower than generic viem decoding. -/
def decodeSponsorParameters (bytes : ByteArray) : Except String SponsorData :=
  match decodeSponsorFields bytes with
  | .error error => .error error
  | .ok fields => acceptCanonicalSponsor bytes fields

/-- Success of the guard implies the native caller supplied at most 12 calls. -/
theorem validated_call_count (calls result : Array ContractCall) (account : Option Nat)
    (h : validateCalls calls account = .ok result) : calls.size ≤ maxContractCalls := by
  unfold validateCalls at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i hnot
    exact Nat.le_of_not_gt hnot

/-- Every accepted sponsor tuple exactly reproduces the complete ABI bytes.
    This is a decoding invariant, independent of the viem vectors. -/
theorem decoded_sponsor_reencodes (bytes : ByteArray) (data : SponsorData)
    (h : decodeSponsorParameters bytes = .ok data) :
    sponsorParameters data = .ok bytes := by
  cases hFields : decodeSponsorFields bytes with
  | error error => simp [decodeSponsorParameters, hFields] at h
  | ok candidate =>
    have hAccept : acceptCanonicalSponsor bytes candidate = .ok data := by
      simpa [decodeSponsorParameters, hFields] using h
    cases hEncode : sponsorParameters candidate with
    | error error => simp [acceptCanonicalSponsor, hEncode] at hAccept
    | ok encoded =>
      by_cases hEqual : encoded == bytes
      · simp [acceptCanonicalSponsor, hEncode, hEqual] at hAccept
        cases hAccept
        have heq : encoded = bytes := byteArray_eq_of_beq hEqual
        simpa [heq] using hEncode
      · simp [acceptCanonicalSponsor, hEncode, hEqual] at hAccept

end Tornado.Protocol.Abi

#print axioms Tornado.Protocol.Abi.validated_call_count
#print axioms Tornado.Protocol.Abi.byteArray_eq_of_beq
#print axioms Tornado.Protocol.Abi.decoded_sponsor_reencodes
