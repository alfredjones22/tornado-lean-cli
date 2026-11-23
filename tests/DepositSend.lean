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
    (failReplace failSend pendingNonce failFinality highFee : Bool) :
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
      | .estimateGas => return toJson ("0x186a0" : String)
      | .feeHistory => return Json.mkObj [
          ("baseFeePerGas", toJson (if highFee then #["0x2540be400", "0x2540be400"]
            else #["0x1", "0x1"])),
          ("reward", toJson #[#["0x1"]])]
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
  catch _ => pure false
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
  let wrongKey ← unwrap "second test key" <|
    parseHexBytes ("0x" ++ String.ofList (List.replicate 63 '0') ++ "2")
  let (mismatchAccepted, _, mismatchSends, mismatchKeyReads) ←
    scenario invoice sender wrongKey readings false false false false false
  require (!mismatchAccepted && mismatchSends == 0 && mismatchKeyReads == 1)
    "A replaced private key reached signing or broadcast."
  IO.println "PASS: invoice planning, durable-before-send fault ordering, ambiguity stop, and exact deposit confirmation"
  return 0
