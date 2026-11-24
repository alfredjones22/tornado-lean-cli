import Lean
import Tornado.Protocol.AbiDecode

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol
open Tornado.Protocol.AbiDecode

private def byteRepeat (count : Nat) (value : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count value)

private def natFromBytes (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def jsonBytes (root : Json) (field : String) : Except String ByteArray := do
  parseHexBytes (← (← root.getObjVal? field).getStr?)

private def abiVector (root : Json) (field : String) : Except String ByteArray := do
  jsonBytes (← root.getObjVal? "cases") field

private def patchBytes (bytes : ByteArray) (start : Nat) (replacement : ByteArray) : ByteArray :=
  bytes.extract 0 start ++ replacement ++ bytes.extract (start + replacement.size) bytes.size

private def patchWord (bytes : ByteArray) (start value : Nat) : Except String ByteArray := do
  return patchBytes bytes start (← Abi.uintWord value)

private def expectFailure {α : Type} (label : String) (result : Except String α) : Except String Unit := do
  if result.isOk then throw s!"Accepted malformed ABI: {label}"

private def checkAbiVectors (root : Json) : Except String Nat := do
  let a : Nat := 0x1111111111111111111111111111111111111111
  let b : Nat := 0x2222222222222222222222222222222222222222
  let short := ByteArray.mk #[0x12, 0x34]
  let expectedCalls : Array Abi.ContractCall := #[
    { to := a, value := 1, data := short },
    { to := b, value := 0, data := ByteArray.empty }]
  let one ← decodeAccountExecuteBatch (← abiVector root "execute_batch_one")
  let two ← decodeAccountExecuteBatch (← abiVector root "execute_batch_two")
  if one != expectedCalls.extract 0 1 || two != expectedCalls then
    throw "Decoded viem batch fields or their order differ."
  let transfer ← decodeErc20Transfer (← abiVector root "transfer_high")
  if transfer != ({ recipient := b, amount := 2 ^ 255 } : Transfer) then
    throw "Decoded viem ERC-20 fields differ."
  let expectedWithdrawal : PoolWithdrawal := {
    proof := short, root := byteRepeat 32 0x11, nullifierHash := byteRepeat 32 0x22,
    recipient := a, relayer := b, fee := 17, refund := 0 }
  let withdrawal ← decodePoolWithdraw (← abiVector root "pool_withdraw_short")
  let emptyWithdrawal ← decodePoolWithdraw (← abiVector root "pool_withdraw_empty")
  if withdrawal != expectedWithdrawal ||
      emptyWithdrawal != { expectedWithdrawal with proof := ByteArray.empty } then
    throw "Decoded viem withdrawal fields differ."
  expectFailure "empty composed batch" (decodeAccountExecuteBatch (← abiVector root "execute_batch_empty"))
  return 5

private def checkRecoveryVectors (root : Json) : Except String Nat := do
  let vectors ← (← root.getObjVal? "vectors").getArr?
  let mut checked := 0
  for vector in vectors do
    let factory ← decodeFactoryCreate (← jsonBytes vector "factoryData")
    let owner := natFromBytes (← jsonBytes vector "owner")
    let salt := natFromBytes (← jsonBytes vector "factorySalt")
    if factory.owner != owner || factory.salt != salt then
      throw "Decoded viem factory fields differ."
    let calls ← decodeAccountExecuteBatch (← jsonBytes vector "data")
    let expected ← (← vector.getObjVal? "calls").getArr?
    if calls.size != expected.size then throw "Decoded recovery call count differs."
    for index in [0:calls.size] do
      let call := calls[index]!
      let item := expected[index]!
      let to := natFromBytes (← jsonBytes item "to")
      let some value := (← (← item.getObjVal? "value").getStr?).toNat?
        | throw "Invalid recovery fixture amount."
      if call.to != to || call.value != value || call.data != (← jsonBytes item "data") then
        throw "Decoded viem recovery call fields differ."
    checked := checked + 2
  if checked != 6 then throw "Unexpected recovery fixture count."
  return checked

private def checkMutations (root recovery : Json) : Except String Nat := do
  let batch ← abiVector root "execute_batch_two"
  let withdrawal ← abiVector root "pool_withdraw_short"
  let transfer ← abiVector root "transfer_high"
  let factory ← jsonBytes (← (← recovery.getObjVal? "vectors").getArr?)[0]! "factoryData"
  let batchMutations : Array (String × ByteArray) := #[
    ("wrong batch selector", patchBytes batch 0 (ByteArray.mk #[0])),
    ("batch truncation", batch.extract 0 (batch.size - 1)),
    ("batch trailing bytes", batch.push 0),
    ("top-level batch offset", ← patchWord batch 4 64),
    ("empty batch count", ← patchWord batch 36 0),
    ("oversized batch count", ← patchWord batch 36 25),
    ("unbounded batch count", ← patchWord batch 36 (2 ^ 255)),
    ("array element points into offsets", ← patchWord batch 68 0),
    ("array tuple gap", ← patchWord batch 68 96),
    ("array tuples overlap", ← patchWord batch 100 64),
    ("array tuple out of bounds", ← patchWord batch 68 (2 ^ 255)),
    ("tuple bytes point into its head", ← patchWord batch 196 64),
    ("tuple bytes out of bounds", ← patchWord batch 196 (2 ^ 255)),
    ("oversized tuple bytes", ← patchWord batch 228 16385),
    ("zero call target", ← patchWord batch 132 0),
    ("nonzero address padding", ← patchWord batch 132 (2 ^ 160)),
    ("nonzero tuple padding", patchBytes batch 291 (ByteArray.mk #[1]))]
  for (label, bytes) in batchMutations do
    expectFailure label (decodeAccountExecuteBatch bytes)
  let withdrawalMutations : Array (String × ByteArray) := #[
    ("wrong pool selector", patchBytes withdrawal 0 (ByteArray.mk #[0])),
    ("pool truncation", withdrawal.extract 0 (withdrawal.size - 1)),
    ("pool trailing bytes", withdrawal.push 0),
    ("pool head overlap", ← patchWord withdrawal 4 192),
    ("pool tail gap", ← patchWord withdrawal 4 256),
    ("pool tail out of bounds", ← patchWord withdrawal 4 (2 ^ 255)),
    ("oversized pool proof", ← patchWord withdrawal 228 16385),
    ("invalid pool recipient", ← patchWord withdrawal 100 (2 ^ 160)),
    ("invalid pool relayer", ← patchWord withdrawal 132 (2 ^ 160)),
    ("nonzero pool padding", patchBytes withdrawal (withdrawal.size - 1) (ByteArray.mk #[1]))]
  for (label, bytes) in withdrawalMutations do
    expectFailure label (decodePoolWithdraw bytes)
  let transferMutations : Array (String × ByteArray) := #[
    ("wrong transfer selector", patchBytes transfer 0 (ByteArray.mk #[0])),
    ("transfer truncation", transfer.extract 0 67),
    ("transfer trailing bytes", transfer.push 0),
    ("invalid transfer recipient", ← patchWord transfer 4 (2 ^ 160))]
  for (label, bytes) in transferMutations do
    expectFailure label (decodeErc20Transfer bytes)
  let factoryMutations : Array (String × ByteArray) := #[
    ("wrong factory selector", patchBytes factory 0 (ByteArray.mk #[0])),
    ("factory truncation", factory.extract 0 67),
    ("factory trailing bytes", factory.push 0),
    ("zero factory owner", ← patchWord factory 4 0),
    ("invalid factory owner", ← patchWord factory 4 (2 ^ 160)),
    ("altered factory salt", ← patchWord factory 36 0)]
  for (label, bytes) in factoryMutations do
    expectFailure label (decodeFactoryCreate bytes)
  -- Canonical field mutations must decode to their new values. This catches
  -- readers that return constants copied from the success fixtures.
  let changedBatch ← decodeAccountExecuteBatch (← patchWord batch 164 99)
  if changedBatch[0]!.value != 99 then throw "Batch value was not independently parsed."
  let changedWithdrawal ← decodePoolWithdraw (← patchWord withdrawal 164 99)
  if changedWithdrawal.fee != 99 then throw "Withdrawal fee was not independently parsed."
  let changedTransfer ← decodeErc20Transfer (← patchWord transfer 36 99)
  if changedTransfer.amount != 99 then throw "Transfer amount was not independently parsed."
  let changedFactory ← decodeFactoryCreate (← patchWord factory 4 99)
  if changedFactory.owner != 99 then throw "Factory owner was not independently parsed."
  return batchMutations.size + withdrawalMutations.size + transferMutations.size + factoryMutations.size

private def checkBounds : Except String Nat := do
  let short : Abi.ContractCall := { to := 1, value := 0, data := ByteArray.empty }
  let full : Abi.ContractCall := { short with data := byteRepeat 16384 0xab }
  -- Decoder boundaries include 24 calls, 16 KiB per call, and 128 KiB total.
  let atCount := Array.replicate 24 short
  if (← decodeAccountExecuteBatch (← Abi.accountExecuteBatchComposed atCount)) != atCount then
    throw "Maximum batch count did not decode."
  let atTotal := Array.replicate 8 full
  if (← decodeAccountExecuteBatch (← Abi.accountExecuteBatchComposed atTotal)) != atTotal then
    throw "Maximum batch data did not decode."
  let maxProof : PoolWithdrawal := {
    proof := full.data, root := byteRepeat 32 1, nullifierHash := byteRepeat 32 2,
    recipient := 1, relayer := 2, fee := 0, refund := 0 }
  if (← decodePoolWithdraw (← encodeWithdrawal maxProof)) != maxProof then
    throw "Maximum proof length did not decode."
  -- Build an otherwise canonical 9-call batch without invoking the composed
  -- encoder's total-data guard, then require the independent reader to reject.
  let oversized ← Abi.accountExecuteBatchComposed (Array.replicate 8 full |>.push short)
  -- Last tuple begins after top offset/length, nine offsets, eight full tuples.
  let lastStart := 4 + 64 + 9 * 32 + 8 * (128 + 16384)
  let larger := (← patchWord oversized (lastStart + 96) 1) ++
    ((ByteArray.mk #[0xab]) ++ byteRepeat 31 0)
  expectFailure "total data over 128 KiB" (decodeAccountExecuteBatch larger)
  expectFailure "raw batch bytes over bound"
    (decodeAccountExecuteBatch (byteRepeat (maxBatchEncodedBytes + 1) 0))
  return 5

def main : IO UInt32 := do
  let abiRaw ← IO.FS.readFile "fixtures/abi-vectors.json"
  let recoveryRaw ← IO.FS.readFile "fixtures/recovery-vectors.json"
  let result := do
    let abi ← Json.parse abiRaw
    let recovery ← Json.parse recoveryRaw
    let vectors ← checkAbiVectors abi
    let recoveryVectors ← checkRecoveryVectors recovery
    let rejected ← checkMutations abi recovery
    let bounds ← checkBounds
    return (vectors + recoveryVectors, rejected, bounds)
  match result with
  | .error error =>
    IO.eprintln error
    return 1
  | .ok (vectors, rejected, bounds) =>
    IO.println s!"PASS: {vectors} independent viem decodes, {rejected} malformed ABI rejections, 4 parsed field mutations, {bounds} bounds checks"
    return 0
