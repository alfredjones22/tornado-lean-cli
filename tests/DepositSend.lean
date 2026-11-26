import Tornado.Cli.DepositSend

open Lean Tornado.Domain Tornado.Cli.DepositSend
open Tornado.Crypto Tornado.Protocol

private def unwrap (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def hex (bytes : ByteArray) : String := "0x" ++ bytesToHex bytes
private def quantity (value : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 value)

private def natBytes (value count : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:count] do
    bytes := bytes.push ((value / 256 ^ (count - 1 - i) % 256).toUInt8)
  return bytes

private def receipt (hashBytes : ByteArray) (sender : Nat)
    (invoice : PublicInvoice) : IO Json := do
  let blockHash := ByteArray.mk (Array.replicate 32 (0x11 : UInt8))
  let commitment ← unwrap "commitment" <| parseHexBytes invoice.commitment
  let pool := invoice.pool.address.toLower
  let senderText := hex (natBytes sender 20)
  let hashText := hex hashBytes
  let blockText := hex blockHash
  let log := Json.mkObj [
    ("address", toJson pool),
    ("topics", toJson #[hex Events.depositTopic, hex commitment]),
    ("data", toJson (hex (natBytes 0 32 ++ natBytes 1 32))),
    ("transactionHash", toJson hashText),
    ("blockHash", toJson blockText),
    ("blockNumber", toJson ("0x1" : String)),
    ("transactionIndex", toJson ("0x0" : String)),
    ("logIndex", toJson ("0x0" : String))]
  return Json.mkObj [
    ("transactionHash", toJson hashText),
    ("blockHash", toJson blockText),
    ("blockNumber", toJson ("0x1" : String)),
    ("transactionIndex", toJson ("0x0" : String)),
    ("from", toJson senderText), ("to", toJson pool),
    ("status", toJson ("0x1" : String)),
    ("logs", Json.arr #[log])]

private def scenario (invoice : PublicInvoice) (sender : Nat)
    (key : ByteArray) (readings : Readings)
    (failReplace failSend pendingNonce failFinality highFee : Bool)
    (estimate : Nat := 1156615) (feeBase : Option Nat := none)
    (priorityFee : Nat := 1)
    (expectedFailure : Option String := none) :
    IO (Bool × ByteArray × Nat × Nat) := do
  let journal ← IO.mkRef ByteArray.empty
  let sends ← IO.mkRef (0 : Nat)
  let keyReads ← IO.mkRef (0 : Nat)
  let approved ← IO.mkRef false
  let lastHash ← IO.mkRef ByteArray.empty
  let effects : Effects := {
    rpc := fun _ method params => do
      match method with
      | .getTransactionCount =>
        if pendingNonce && params[1]? == some (toJson ("pending" : String)) then
          return toJson ("0x1" : String)
        return toJson ("0x0" : String)
      | .estimateGas => return toJson (quantity estimate)
      | .feeHistory =>
        let base := feeBase.getD (if highFee then 10000000000 else 1)
        return Json.mkObj [
          ("baseFeePerGas", toJson (#[quantity base, quantity base])),
          ("reward", toJson (#[#[quantity priorityFee]]))]
      | .getBalance => return toJson ("0xde0b6b3a7640000" : String)
      | .sendRawTransaction =>
        sends.modify (· + 1)
        let raw ← unwrap "raw transaction" <| parseHexBytes
          (← unwrap "raw argument" <| params[0]!.getStr?)
        let hashBytes := keccak256 raw
        lastHash.set hashBytes
        if failSend then throw <| IO.userError "simulated ambiguous transport failure"
        return toJson (hex hashBytes)
      | .getTransactionReceipt =>
        return (← receipt (← lastHash.get) sender invoice)
      | _ => throw <| IO.userError "unexpected RPC method in deposit test",
    createJournal := fun initial => journal.set initial,
    replaceJournal := fun expected next => do
      if (← journal.get) != expected then
        throw <| IO.userError "journal compare-and-replace lost prior bytes"
      if failReplace then throw <| IO.userError "simulated journal fsync failure"
      journal.set next,
    sign := fun tx => do
      require (← approved.get) "Signing key was used before approval."
      require (!(← journal.get).isEmpty) "Signing key was used before the planned journal."
      require (tx.gas == estimate * 120 / 100 + 1)
        "Signed transaction did not retain the buffered gas estimate."
      require (tx.maxFeePerGas == 2 * feeBase.getD (if highFee then 10000000000 else 1) +
        priorityFee) "Signed transaction changed the reviewed maximum fee quote."
      keyReads.modify (· + 1)
      let signerBytes ← unwrap "test sender" <| secp256k1EthereumAddress key
      let actualSender := signerBytes.data.foldl
        (fun n byte => n * 256 + byte.toNat) 0
      let signed ← unwrap "test signer" <| TypedTransaction.sign1559 tx key
      return (actualSender, signed),
    waitFinality := fun _ =>
      if failFinality then throw <| IO.userError "simulated confirmation-depth failure"
      else pure (),
    approve := fun _ => approved.set true }
  let result ← try
    let _ ← executeWith effects invoice sender readings
    pure true
  catch error =>
    if let some expected := expectedFailure then
      require ((error.toString.splitOn expected).length > 1)
        s!"Expected {expected}, got {error}."
    pure false
  return (result, ← journal.get, ← sends.get, ← keyReads.get)

def main : IO UInt32 := do
  let key ← unwrap "test private key" <|
    parseHexBytes ("0x" ++ String.ofList (List.replicate 63 '0') ++ "1")
  let senderBytes ← unwrap "derive test sender" <| secp256k1EthereumAddress key
  let sender := senderBytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let some pool := poolFor .mainnet "0.01" "ETH"
    | throw <| IO.userError "Missing public ETH fixture pool."
  let commitment := "0x" ++ String.ofList (List.replicate 64 '1')
  let invoiceText ← unwrap "public invoice" <| invoiceForNote pool commitment
  let invoice ← unwrap "parse public invoice" <| parseInvoice invoiceText .mainnet
  let readings : Readings := ⟨1, pool.amount, 1000000000000000000, 0, 0⟩
  require (valueGasDivisor pool.amount == 0 &&
    gasCostLimit pool.amount == 20000000000000000 &&
    valueGasDivisor (pool.amount - 1) == 0 &&
    gasCostLimit (pool.amount - 1) == 20000000000000000 &&
    valueGasDivisor 0 == 0 &&
    valueGasDivisor (pool.amount + 1) == 10 &&
    gasCostLimit (pool.amount + 1) == (pool.amount + 1) / 10)
    "Small ETH deposit fee policy changed at the inclusive 0.01 ETH boundary."
  let steps ← unwrap "ETH invoice plan" <| planInvoice invoice sender readings
  require (steps.size == 1 && steps[0]!.kind == .deposit &&
    steps[0]!.value == pool.amount)
    "ETH invoice did not yield exactly one value-bearing deposit."
  require (!(planInvoice invoice sender { readings with chainId := 11155111 }).isOk &&
    !(planInvoice invoice sender { readings with denomination := 1 }).isOk &&
    !(planInvoice invoice sender { readings with ethBalance := pool.amount }).isOk)
    "Invoice planner accepted a wrong chain, denomination, or balance."
  let some tokenPool := poolFor .mainnet "100" "USDC"
    | throw <| IO.userError "Missing public USDC fixture pool."
  let tokenText ← unwrap "token invoice" <| invoiceForNote tokenPool commitment
  let tokenInvoice ← unwrap "parse token invoice" <| parseInvoice tokenText .mainnet
  let tokenSteps ← unwrap "token invoice plan" <| planInvoice tokenInvoice sender
    ⟨1, tokenPool.amount, 1, tokenPool.amount, 1⟩
  require (tokenSteps.size == 3 && tokenSteps[0]!.kind == .reset &&
    tokenSteps[1]!.kind == .approve && tokenSteps[2]!.kind == .deposit)
    "Nonzero insufficient allowance did not yield reset, exact approval, deposit."
  let (writeSucceeded, writeJournal, writeSends, writeKeyReads) ←
    scenario invoice sender key readings true false false false false
  let writeText := (String.fromUTF8? writeJournal).getD ""
  require (!writeSucceeded && writeSends == 0 && writeKeyReads == 1 &&
    (writeText.splitOn "planned").length > 1)
    "A failed prepared-journal write exposed a signed transaction."
  let (sendSucceeded, sendJournal, sendCount, sendKeyReads) ←
    scenario invoice sender key readings false true false false false
  require (!sendSucceeded && sendCount == 1 && sendKeyReads == 1 &&
    (((String.fromUTF8? sendJournal).getD "").splitOn "prepared").length > 1)
    "Ambiguous broadcast did not retain the prepared hash."
  let (confirmed, confirmedJournal, confirmedSends, confirmedKeyReads) ←
    scenario invoice sender key readings false false false false false
  require (confirmed && confirmedSends == 1 && confirmedKeyReads == 1 &&
    (((String.fromUTF8? confirmedJournal).getD "").splitOn "confirmed").length > 1)
    "Exact receipt and Deposit event did not confirm the deposit."
  let (observed, _, observedSends, observedKeyReads) ←
    scenario invoice sender key readings false false false false false
      1156615 (some 0) 1000000000
  require (1156615 * 120 / 100 + 1 == 1387939 &&
    1387939 * 1000000000 > pool.amount / 10 &&
    observed && observedSends == 1 && observedKeyReads == 1)
    "Observed 0.01 ETH estimate and 1 gwei fee were blocked by the old 10% cap."
  let some largerPool := poolFor .mainnet "0.1" "ETH"
    | throw <| IO.userError "Missing larger ETH fixture pool."
  let largerText ← unwrap "larger public invoice" <| invoiceForNote largerPool commitment
  let largerInvoice ← unwrap "parse larger invoice" <|
    parseInvoice largerText .mainnet
  let largerReadings : Readings :=
    ⟨1, largerPool.amount, 1000000000000000000, 0, 0⟩
  let (relativeAccepted, _, relativeSends, relativeKeyReads) ←
    scenario largerInvoice sender key largerReadings false false false false false
      1156615 (some 5000000000) 1000000000
      (some "The quoted maximum gas cost exceeds the safety cap.")
  require (1387939 * 11000000000 > largerPool.amount / 10 &&
    1387939 * 11000000000 < 20000000000000000 &&
    !relativeAccepted && relativeSends == 0 && relativeKeyReads == 0)
    "A deposit above 0.01 ETH bypassed the retained 10% fee cap."
  let (absoluteAccepted, _, absoluteSends, absoluteKeyReads) ←
    scenario invoice sender key readings false false false false false
      1156615 (some 7000000000) 1000000000
      (some "The quoted maximum gas cost exceeds the safety cap.")
  require (1387939 * 15000000000 > 20000000000000000 &&
    !absoluteAccepted && absoluteSends == 0 && absoluteKeyReads == 0)
    "A 0.01 ETH deposit bypassed the retained 0.02 ETH absolute cap."
  let (pendingAccepted, _, pendingSends, pendingKeyReads) ←
    scenario invoice sender key readings false false true false false
  require (!pendingAccepted && pendingSends == 0 && pendingKeyReads == 0)
    "A pending nonce could replace another transaction or read the signing key."
  let (depthAccepted, depthJournal, depthSends, depthKeyReads) ←
    scenario invoice sender key readings false false false true false
  require (!depthAccepted && depthSends == 1 && depthKeyReads == 1 &&
    (((String.fromUTF8? depthJournal).getD "").splitOn "submitted").length > 1)
    "An unfinalized receipt was marked confirmed or another transaction could proceed."
  let (feeAccepted, _, feeSends, feeKeyReads) ←
    scenario invoice sender key readings false false false false true
  require (!feeAccepted && feeSends == 0 && feeKeyReads == 0)
    "An excessive RPC fee quote reached key read, signing, or broadcast."
  for estimate in [0, 1666667] do
    let (gasAccepted, gasJournal, gasSends, gasKeyReads) ←
      scenario invoice sender key readings false false false false false estimate
    require (!gasAccepted && gasSends == 0 && gasKeyReads == 0 &&
      (((String.fromUTF8? gasJournal).getD "").splitOn "planned").length > 1)
      "A zero or excessive buffered gas estimate reached signing or broadcast."
  let wrongKey ← unwrap "second test key" <|
    parseHexBytes ("0x" ++ String.ofList (List.replicate 63 '0') ++ "2")
  let (mismatchAccepted, _, mismatchSends, mismatchKeyReads) ←
    scenario invoice sender wrongKey readings false false false false false
  require (!mismatchAccepted && mismatchSends == 0 && mismatchKeyReads == 1)
    "A replaced private key reached signing or broadcast."
  IO.println "PASS: invoice planning, durable-before-send fault ordering, ambiguity stop, and exact deposit confirmation"
  return 0
