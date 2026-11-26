import Tornado.Cli.DepositMulti
import Tornado.Domain.Simple7702

open Lean Tornado.Domain Tornado.Cli.DepositMulti

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def word (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:32] do
    bytes := bytes.push ((value / 256 ^ (31 - i) % 256).toUInt8)
  return bytes

private def addressNat (raw : String) : IO Nat := do
  let bytes ← unwrap "catalog address" <| parseHexBytes raw
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

def main : IO UInt32 := do
  let some ethA := poolFor .mainnet "0.01" "ETH"
    | throw <| IO.userError "Missing ETH fixture pool."
  let some ethB := poolFor .mainnet "0.1" "ETH"
    | throw <| IO.userError "Missing second ETH fixture pool."
  let ethItems : Array Item := #[⟨ethA, word 1⟩, ⟨ethB, word 2⟩]
  let ethReadings : Readings := ⟨1, ByteArray.empty,
    1000000000000000000, 0,
    #[⟨(← addressNat ethA.address), ethA.amount, 0⟩,
      ⟨(← addressNat ethB.address), ethB.amount, 0⟩]⟩
  let batch ← unwrap "two ETH notes" <| plan ethItems .mainnet 123 ethReadings
  require (batch.mode == .simple7702 && batch.reason == .undelegatedEOA &&
      batch.batches.size == 1 && batch.batches[0]!.size == 2 &&
      batch.amount == ethA.amount + ethB.amount)
    "Two undelegated ETH deposits did not produce one Simple7702 batch."
  let sequential ← unwrap "contract/delegated sender" <| plan ethItems .mainnet 123
    { ethReadings with senderCode := ByteArray.empty.push 0xef }
  require (sequential.mode == .sequential &&
    sequential.reason == .contractOrDelegated && sequential.batches[0]!.size == 2)
    "Existing sender code did not select sequential deposits."
  let forced ← unwrap "forced sequential" <| plan ethItems .mainnet 123
    ethReadings true
  require (forced.mode == .sequential && forced.reason == .forcedSequential)
    "Explicit sequential request was ignored."
  let compatibleReadings := { ethReadings with senderCode := Simple7702.designator }
  let compatible ← unwrap "compatible delegation" <|
    plan ethItems .mainnet 123 compatibleReadings
  require (Simple7702.isDelegation Simple7702.designator &&
    Simple7702.isCompatible Simple7702.designator &&
    compatible.mode == .simple7702 && compatible.reason == .compatibleDelegation)
    "Exact pinned 23-byte delegation did not select batch reuse."
  let compatibleOne ← unwrap "one note with compatible delegation" <|
    plan #[ethItems[0]!] .mainnet 123 compatibleReadings
  require (compatibleOne.mode == .sequential &&
    compatibleOne.reason == .singleDeposit && compatibleOne.batches.size == 1)
    "One note with an existing compatible delegation did not default to an ordinary transaction."
  let foreignCode := Simple7702.delegationPrefix ++ (word 123).extract 12 32
  let foreignReadings := { ethReadings with senderCode := foreignCode }
  let foreignDefault ← unwrap "foreign delegation defaults sequential" <|
    plan ethItems .mainnet 123 foreignReadings
  require (Simple7702.isDelegation foreignCode &&
    !Simple7702.isCompatible foreignCode &&
    foreignDefault.mode == .sequential && foreignDefault.reason == .contractOrDelegated)
    "A foreign designator entered batching without explicit delegation."
  let replace ← unwrap "forced delegation replacement" <|
    plan ethItems .mainnet 123 foreignReadings false true
  require (replace.mode == .simple7702 && replace.reason == .forcedDelegated)
    "Forced delegation did not route a valid foreign designator to batches."
  let forcedOne ← unwrap "forced delegation for one note" <|
    plan #[ethItems[0]!] .mainnet 123 ethReadings false true
  require (forcedOne.mode == .simple7702 && forcedOne.reason == .forcedDelegated)
    "Explicit delegation did not route an undelegated one-note deposit to a batch."
  let compatibleForced ← unwrap "explicit compatible delegation" <|
    plan ethItems .mainnet 123 compatibleReadings false true
  require (compatibleForced.mode == .simple7702 && compatibleForced.reason == .forcedDelegated)
    "Explicit delegation did not preserve compatible reuse semantics."
  require (!(plan ethItems .mainnet 123 foreignReadings true true).isOk &&
    !(plan ethItems .mainnet 123
      { ethReadings with senderCode := ByteArray.mk #[0x60, 0x00] } false true).isOk &&
    !(plan ethItems .mainnet 123
      { ethReadings with senderCode := Simple7702.designator.extract 0 22 } false true).isOk &&
    !Simple7702.isDelegation (Simple7702.designator.extract 0 22))
    "Conflicting flags, contract code, or truncated designator was accepted."
  let single ← unwrap "one direct deposit" <|
    plan #[ethItems[0]!] .mainnet 123 ethReadings
  require (single.mode == .sequential && single.reason == .singleDeposit)
    "A single approval-free deposit did not use an ordinary transaction."
  for senderCode in [foreignCode, ByteArray.mk #[0x60, 0x00]] do
    let one ← unwrap "one note with other sender code" <|
      plan #[ethItems[0]!] .mainnet 123 { ethReadings with senderCode }
    require (one.mode == .sequential && one.reason == .singleDeposit)
      "Sender code overrode the single-note default."
  require (!(plan ethItems .sepolia 123 ethReadings).isOk &&
    !(plan ethItems .mainnet 123 { ethReadings with chainId := 11155111 }).isOk &&
    !(plan ethItems .mainnet 123 { ethReadings with ethBalance := batch.amount }).isOk &&
    !(plan ethItems .mainnet 123
      { ethReadings with pools := #[⟨(← addressNat ethA.address), 1, 0⟩,
        ⟨(← addressNat ethB.address), ethB.amount, 0⟩] }).isOk &&
    !(plan #[ethItems[0]!, ethItems[0]!] .mainnet 123 ethReadings).isOk)
    "Wrong chain, denomination, balance, or duplicate commitment was accepted."
  let creditReadings := { compatibleReadings with ethBalance := batch.amount }
  let credited ← unwrap "owned EntryPoint credit covers batch gas" <|
    plan ethItems .mainnet 123 creditReadings false false 1
  require (credited.mode == .simple7702 &&
    !(plan ethItems .mainnet 123 creditReadings true false 1).isOk &&
    !(plan ethItems .mainnet 123
      { creditReadings with senderCode := foreignCode } false false 1).isOk &&
    !(plan ethItems .mainnet 123
      { creditReadings with ethBalance := batch.amount - 1 } false false (10 ^ 20)).isOk &&
    !(plan ethItems .mainnet 123 ethReadings false false Tornado.Protocol.Abi.maxUint256).isOk)
    "Gas credit changed sequential routing, funded ETH principal, or exceeded uint256."
  let singleCreditReadings := { compatibleReadings with ethBalance := ethItems[0]!.pool.amount }
  require (!(plan #[ethItems[0]!] .mainnet 123 singleCreditReadings false false 1).isOk &&
    (plan #[ethItems[0]!] .mainnet 123 singleCreditReadings false true 1).isOk)
    "Gas credit implicitly delegated a single note or blocked explicit delegation."
  let some usdc := poolFor .mainnet "100" "USDC"
    | throw <| IO.userError "Missing USDC fixture pool."
  let mut tokenItems := #[]
  for i in [1:7] do tokenItems := tokenItems.push ⟨usdc, word i⟩
  let tokenReadings : Readings := ⟨1, ByteArray.empty,
    1000000000000000000, usdc.amount * 6,
    #[⟨(← addressNat usdc.address), usdc.amount, 1⟩]⟩
  let tokenCreditReadings := { tokenReadings with ethBalance := 0 }
  require ((plan tokenItems .mainnet 123 tokenCreditReadings false false 1).isOk &&
    !(plan tokenItems .mainnet 123 tokenCreditReadings true false 1).isOk &&
    !(plan tokenItems .mainnet 123 tokenCreditReadings).isOk &&
    !(plan tokenItems .mainnet 123
      { tokenCreditReadings with tokenBalance := usdc.amount * 6 - 1 } false false 1).isOk)
    "Gas credit did not remain separate from token principal or ordinary transaction gas."
  for senderCode in [ByteArray.empty, Simple7702.designator] do
    let one ← unwrap "one token note requiring reset and approval" <|
      plan #[tokenItems[0]!] .mainnet 123 { tokenReadings with senderCode }
    require (one.mode == .sequential && one.reason == .singleDeposit &&
      one.batches[0]!.size == 3 && one.batches[0]![0]!.kind == .reset &&
      one.batches[0]![1]!.kind == .approve && one.batches[0]![2]!.kind == .deposit)
      "One token note implicitly enabled a UserOperation because approvals were required."
    let delegated ← unwrap "explicit single-token batch" <|
      plan #[tokenItems[0]!] .mainnet 123 { tokenReadings with senderCode } false true
    require (delegated.mode == .simple7702 && delegated.reason == .forcedDelegated &&
      delegated.batches[0]!.size == 3)
      "--delegated did not override the single-token default."
  let tokenBatch ← unwrap "six token notes" <|
    plan tokenItems .mainnet 123 tokenReadings
  require (tokenBatch.mode == .simple7702 &&
    tokenBatch.batches.size == 2 &&
    tokenBatch.batches[0]!.size == 6 &&
    tokenBatch.batches[1]!.size == 2 &&
    tokenBatch.batches[0]![0]!.kind == .reset &&
    tokenBatch.batches[0]![1]!.kind == .approve &&
    tokenBatch.batches[0]![1]!.approvalAmount == usdc.amount * 4)
    "Token batch did not avoid a singleton tail or approve its exact first chunk."
  let tokenSeq ← unwrap "six sequential token notes" <|
    plan tokenItems .mainnet 123 tokenReadings true
  require (tokenSeq.mode == .sequential && tokenSeq.batches.size == 1 &&
    tokenSeq.batches[0]!.size == 8 &&
    tokenSeq.batches[0]![1]!.approvalAmount == usdc.amount * 6)
    "Sequential token plan did not approve the full selected amount."
  let noteA := "tornado-eth-0.01-1-0x33567fb6463d588b0ef7ff2d415130e0d91059781005f504671ddc3f03c4adc8b873cfa627a16e46d1f33b81d9c7e86772a083575ccccb9104ed77057b53"
  let noteB := "tornado-eth-1-1-0x38ba0d601404fd62799e1f48f412425062db944406ad748338cdf17cc91e1b0e52370aca05d3731e2f6e278d0fb871ecedf5a9de9a20969a636b16acde90"
  let parsed ← unwrap "native private backup reduction" <|
    publicItems (noteA ++ "\n" ++ noteB) .mainnet
  require (parsed.size == 2 && parsed.all (fun item => item.commitment.size == 32))
    "Private backup did not reduce to two public bytes32 commitments."
  IO.println "PASS: multi-note sequential/7702 planning, approval and chunk limits, and private-backup reduction"
  return 0
