import Tornado.Cli.RecoverySend

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.SmartAccount Tornado.Cli Tornado.Cli.RecoverySend

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def rejects (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def key : ByteArray :=
  ⟨Array.replicate 31 0 |>.push 1⟩

private def word (value size : Nat) : ByteArray := Id.run do
  let mut output := ByteArray.empty
  for i in [0:size] do
    output := output.push ((value / 256 ^ (size - 1 - i) % 256).toUInt8)
  return output

private def fixtureReview : IO SmartAccountRecover.Review := do
  let ownerBytes ← checked <| secp256k1EthereumAddress key
  let owner := ownerBytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let account ← checked <| Tornado.SmartAccount.Address.predict owner
  let mut balances := Array.replicate (assetsFor .mainnet).length 0
  balances := balances.set! 0 10000000000000000
  let plan ← checked <| planRecovery .mainnet owner account 3 balances 42
  return ⟨.mainnet, 100, ⟨owner, account, true, 0⟩, plan⟩

private inductive Fault where
  | none | preparedWrite | broadcast | changedReview | replaceWrite
  | wrongKey | highFee | finality | wrongReceipt | reverted
  deriving BEq

private structure Result where
  success : Bool
  journal : ByteArray
  sends : Nat
  signatures : Nat
  events : List String
  transaction : Json
  receipt : Json

private def scenario (review : SmartAccountRecover.Review)
    (fault : Fault := .none) : IO Result := do
  let journal ← IO.mkRef ByteArray.empty
  let sends ← IO.mkRef (0 : Nat)
  let signatures ← IO.mkRef (0 : Nat)
  let events ← IO.mkRef ([] : List String)
  let txRef ← IO.mkRef (default : Rlp.Transaction1559)
  let hashRef ← IO.mkRef ByteArray.empty
  let note (event : String) := events.modify (· ++ [event])
  let blockHash := word 123 32
  let txJson : IO Json := do
    let tx ← txRef.get
    return Json.mkObj [
      ("hash", toJson (ProtectedTxSender.hex (← hashRef.get))),
      ("from", toJson (← checked <| ProtectedTxSender.address review.plan.owner)),
      ("to", toJson (← checked <| ProtectedTxSender.address review.plan.account)),
      ("input", toJson (ProtectedTxSender.hex tx.data)),
      ("chainId", toJson (ProtectedTxSender.quantity tx.chainId)),
      ("type", toJson ("0x2" : String)),
      ("nonce", toJson (ProtectedTxSender.quantity tx.nonce)),
      ("value", toJson (ProtectedTxSender.quantity tx.value)),
      ("gas", toJson (ProtectedTxSender.quantity tx.gas)),
      ("maxFeePerGas", toJson (ProtectedTxSender.quantity tx.maxFeePerGas)),
      ("maxPriorityFeePerGas", toJson (ProtectedTxSender.quantity tx.maxPriorityFeePerGas)),
      ("blockHash", toJson (ProtectedTxSender.hex blockHash)),
      ("blockNumber", toJson ("0x64" : String)),
      ("transactionIndex", toJson ("0x0" : String))]
  let receiptJson : IO Json := do
    return Json.mkObj [
      ("transactionHash", toJson (ProtectedTxSender.hex (← hashRef.get))),
      ("blockHash", toJson (ProtectedTxSender.hex blockHash)),
      ("blockNumber", toJson ("0x64" : String)),
      ("transactionIndex", toJson ("0x0" : String)),
      ("from", toJson (← checked <| ProtectedTxSender.address review.plan.owner)),
      ("to", toJson (← checked <| ProtectedTxSender.address
        (if fault == .wrongReceipt then 4 else review.plan.account))),
      ("status", toJson (if fault == .reverted then "0x0" else "0x1")),
      ("logs", Json.arr #[])]
  let effects : RecoverySend.Effects := {
    rpc := fun _ method params => do
      match method with
      | .chainId => return toJson ("0x1" : String)
      | .getTransactionCount => return toJson ("0x0" : String)
      | .estimateGas => return toJson ("0x186a0" : String)
      | .feeHistory => return Json.mkObj [
        ("baseFeePerGas", toJson (if fault == .highFee then
          #["0x174876e800", "0x174876e800"] else #["0x1", "0x1"])),
        ("reward", toJson #[#["0x1"]])]
      | .getBalance => return toJson ("0xde0b6b3a7640000" : String)
      | .sendRawTransaction =>
        note "broadcast"
        sends.modify (· + 1)
        let prepared ← checked <| SmartAccountStatus.parseJournal
          ((String.fromUTF8? (← journal.get)).getD "")
        require (prepared.priorStatus == .prepared)
          "Recovery broadcast preceded the prepared journal."
        let raw ← checked <| parseHexBytes (← checked params[0]!.getStr?)
        require (keccak256 raw == prepared.transactionHash)
          "Recovery journal recorded another signed hash."
        if fault == .broadcast then throw <| IO.userError "ambiguous public fixture send"
        return toJson (ProtectedTxSender.hex (keccak256 raw))
      | .getTransactionReceipt => return (← receiptJson)
      | .getTransactionByHash => return (← txJson)
      | _ => throw <| IO.userError "Unexpected public recovery fixture RPC"
    sign := fun tx => do
      note "sign"
      signatures.modify (· + 1)
      txRef.set tx
      let signed ← checked <| TypedTransaction.sign1559 tx key
      hashRef.set signed.transactionHash
      return (if fault == .wrongKey then review.plan.owner + 1 else review.plan.owner, signed)
    approve := fun _ => note "approve"
    rereview := do
      note "rereview"
      if fault == .changedReview then
        let changed ← checked <| planRecovery review.chainId review.plan.owner
          review.plan.account 4 review.plan.balances review.plan.entryPointDeposit
        return { review with plan := changed }
      return review
    createJournal := fun bytes => do
      note "prepared"
      if fault == .preparedWrite then throw <| IO.userError "simulated prepared fsync failure"
      require ((← journal.get).isEmpty) "Recovery overwrote an existing attempt."
      journal.set bytes
    replaceJournal := fun prior next => do
      require ((← journal.get) == prior) "Recovery CAS lost prior bytes."
      if fault == .replaceWrite then throw <| IO.userError "simulated replacement fsync failure"
      let parsed ← checked <| SmartAccountStatus.parseJournal
        ((String.fromUTF8? next).getD "")
      note parsed.priorStatus.text
      journal.set next
    waitFinality := fun _ => do
      note "finality"
      if fault == .finality then throw <| IO.userError "simulated reorg" }
  let success ← try
    let _ ← executeWith effects review { receiptPolls := 1, receiptPollMs := 0 }
    pure true
    catch _ => pure false
  return {
    success := success
    journal := ← journal.get
    sends := ← sends.get
    signatures := ← signatures.get
    events := ← events.get
    transaction := ← txJson
    receipt := ← receiptJson }

private def status (result : Result) : IO SmartAccountStatus.Status := do
  let journal ← checked <| SmartAccountStatus.parseJournal
    ((String.fromUTF8? result.journal).getD "")
  return journal.priorStatus

def main : IO UInt32 := do
  let review ← fixtureReview
  let _ ← checked <| validateReview review
  let goodTx : Rlp.Transaction1559 := {
    chainId := 1
    nonce := 0
    gas := 120001
    maxFeePerGas := 3
    maxPriorityFeePerGas := 1
    to := some review.plan.account
    value := 0
    data := review.plan.data }
  let _ ← checked <| validateCandidate review goodTx
  for tx in #[{ goodTx with chainId := 11155111 },
      { goodTx with to := some 4 }, { goodTx with value := 1 },
      { goodTx with data := ByteArray.empty }, { goodTx with gas := 0 }] do
    require (!(validateCandidate review tx).isOk)
      "Changed recovery candidate reached the sender boundary."
  let good ← scenario review
  require (good.success && good.sends == 1 && good.signatures == 1 &&
      (← status good) == .confirmed &&
      good.events == ["approve", "rereview", "sign", "prepared", "broadcast",
        "submitted", "finality", "confirmed"])
    "Recovery did not preserve approval, revalidation, durable journal and confirmation order."
  let failedWrite ← scenario review .preparedWrite
  require (!failedWrite.success && failedWrite.sends == 0 && failedWrite.signatures == 1)
    "Failed recovery journal creation exposed a signed transaction."
  let ambiguous ← scenario review .broadcast
  require (!ambiguous.success && ambiguous.sends == 1 && ambiguous.signatures == 1 &&
      (← status ambiguous) == .unknown)
    "Ambiguous recovery broadcast retried or lost the recorded hash."
  let changed ← scenario review .changedReview
  require (!changed.success && changed.sends == 0 && changed.signatures == 0)
    "Changed recovery review reached the signing key."
  let failedCAS ← scenario review .replaceWrite
  require (!failedCAS.success && failedCAS.sends == 1 && failedCAS.signatures == 1 &&
      (← status failedCAS) == .prepared)
    "Failed post-exposure CAS caused replacement or lost the prepared hash."
  let wrongKey ← scenario review .wrongKey
  require (!wrongKey.success && wrongKey.sends == 0)
    "Changed owner key reached recovery broadcast."
  let highFee ← scenario review .highFee
  require (!highFee.success && highFee.sends == 0 && highFee.signatures == 0)
    "Excessive recovery fee reached the signing key."
  for fault in #[Fault.finality, .wrongReceipt] do
    let result ← scenario review fault
    require (!result.success && result.sends == 1 && result.signatures == 1 &&
      (← status result) == .unknown)
      "Bad recovery receipt or finality evidence was confirmed."
  let reverted ← scenario review .reverted
  require (!reverted.success && reverted.sends == 1 && (← status reverted) == .failed)
    "A reverted recovery transaction was not retained as failed."
  let casWrites ← IO.mkRef (0 : Nat)
  let fetch : JsonRpc.Method → Array Json → IO Json := fun method _ =>
    match method with
    | .chainId => pure <| toJson ("0x1" : String)
    | .getTransactionByHash => pure good.transaction
    | .getTransactionReceipt => pure good.receipt
    | _ => throw <| IO.userError "Unexpected reconciliation fixture RPC"
  let (_, observed) ← SmartAccountStatus.reconcileWith ambiguous.journal fetch fun prior next => do
    require (prior == ambiguous.journal) "Recovery status replaced a different journal snapshot."
    let parsed ← checked <| SmartAccountStatus.parseJournal ((String.fromUTF8? next).getD "")
    require (parsed.priorStatus == .confirmed) "Recovery CAS did not persist exact confirmation."
    casWrites.modify (· + 1)
  require (observed.status == .confirmed && (← casWrites.get) == 1)
    "Recovery status did not persist the exact chain observation."
  require (← rejects <| SmartAccountStatus.reconcileWith good.journal fetch
    (fun _ _ => throw <| IO.userError "stale CAS"))
    "Recovery status hid a failed or stale journal replacement."
  let badAccount := { review with
    account := { review.account with address := review.account.address + 1 }
    plan := { review.plan with account := review.account.address + 1 } }
  require (!(validateReview badAccount).isOk)
    "An RPC-selected destination bypassed local account prediction."
  let creates ← IO.mkRef (0 : Nat)
  let removals ← IO.mkRef (0 : Nat)
  let createLock := creates.modify (· + 1)
  let removeLock := removals.modify (· + 1)
  let cancelled (_ : IO Unit) : IO Unit := throw <| IO.userError "cancelled before signing"
  let unknown (started : IO Unit) : IO Unit := do
    started
    throw <| IO.userError "unknown after signing"
  require (← rejects <| withSenderLock createLock removeLock cancelled)
    "Recovery cancellation unexpectedly succeeded."
  require ((← creates.get) == 1 && (← removals.get) == 1)
    "Pre-signing cancellation retained the sender lock."
  require (← rejects <| withSenderLock createLock removeLock unknown)
    "Unknown recovery outcome unexpectedly succeeded."
  require ((← creates.get) == 2 && (← removals.get) == 1)
    "An unknown signed recovery released its sender lock."
  let _ ← withSenderLock createLock removeLock fun started => do
    started
    pure ()
  require ((← creates.get) == 3 && (← removals.get) == 2)
    "Exact successful completion failed to release the sender lock."
  for args in [
      ["--experimental-send"],
      ["--experimental-send", "--owner-key-file", "/missing"],
      ["--experimental-send", "--journal", "/missing"],
      ["--experimental-send", "--dry-run"],
      ["--experimental-send", "--yes"]] do
    require (← rejects <| RecoverySend.recoverCommand args)
      "An invalid live recovery command reached a network or signing operation."
  IO.println "PASS: recovery candidate binding, review revalidation, journal-before-send fault traces, and status CAS"
  return 0
