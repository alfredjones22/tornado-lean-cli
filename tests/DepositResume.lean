import Tornado.Cli.DepositResume
import Tornado.Cli.DepositStatus

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Cli

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def reportedBound (failure : Option String) (wei : Nat) : Bool :=
  match failure with
  | none => false
  | some message => (message.splitOn s!"({wei} wei)").length > 1

private def bytes (number count : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:count] do
    result := result.push ((number / 256 ^ (count - 1 - i) % 256).toUInt8)
  return result

private def hex := ProtectedTxSender.hex
private def quantity := ProtectedTxSender.quantity

private def receipt (sender : Nat) (tx : Rlp.Transaction1559)
    (hash : ByteArray) (wrongEvent : Bool) : Json := Id.run do
  let target := tx.to.getD 0
  let blockHash := bytes 17 32
  let commitment := if wrongEvent then bytes 999 32 else tx.data.extract 4 36
  let log := Json.mkObj [
    ("address", toJson (hex (bytes target 20))),
    ("topics", toJson #[hex Events.depositTopic, hex commitment]),
    ("data", toJson (hex (bytes 0 32 ++ bytes 1 32))),
    ("transactionHash", toJson (hex hash)), ("blockHash", toJson (hex blockHash)),
    ("blockNumber", toJson ("0x1" : String)),
    ("transactionIndex", toJson ("0x0" : String)),
    ("logIndex", toJson ("0x0" : String))]
  return Json.mkObj [("transactionHash", toJson (hex hash)),
    ("blockHash", toJson (hex blockHash)), ("blockNumber", toJson ("0x1" : String)),
    ("transactionIndex", toJson ("0x0" : String)),
    ("from", toJson (hex (bytes sender 20))),
    ("to", toJson (hex (bytes target 20))),
    ("status", toJson ("0x1" : String)), ("logs", Json.arr #[log])]

private def indexed (sender : Nat) (tx : Rlp.Transaction1559)
    (hash : ByteArray) (wrongInput : Bool) : Json :=
  Json.mkObj [("hash", toJson (hex hash)),
    ("from", toJson (hex (bytes sender 20))),
    ("to", toJson (hex (bytes (tx.to.getD 0) 20))),
    ("chainId", toJson (quantity tx.chainId)), ("type", toJson ("0x2" : String)),
    ("nonce", toJson (quantity tx.nonce)), ("value", toJson (quantity tx.value)),
    ("gas", toJson (quantity tx.gas)),
    ("maxFeePerGas", toJson (quantity tx.maxFeePerGas)),
    ("maxPriorityFeePerGas", toJson (quantity tx.maxPriorityFeePerGas)),
    ("input", toJson (hex (if wrongInput then ByteArray.empty else tx.data))),
    ("blockHash", toJson (hex (bytes 17 32))),
    ("blockNumber", toJson ("0x1" : String)),
    ("transactionIndex", toJson ("0x0" : String))]


private def scenario (fault : String := "") (preview : Bool := false) (mixed : Bool := false) : IO Unit := do
  let key := bytes 1 32
  let publicAddress ← checked <| secp256k1EthereumAddress key
  let sender := publicAddress.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let some pool := poolFor .mainnet "0.01" "ETH" | throw <| IO.userError "Missing fixture pool."
  let items : Array DepositMulti.Item ← (List.range 6).toArray.mapM fun i => do
    let denomination := if mixed && i == 0 then "1" else if mixed && i < 5 then "0.1" else "0.01"
    let some selected := poolFor .mainnet denomination "ETH"
      | throw <| IO.userError "Missing mixed denomination fixture."
    return ⟨selected, bytes (i + 1) 32⟩
  let steps ← checked <| items.mapM DepositMulti.depositStep
  let transactions ← (steps.extract 0 5).mapIdxM fun i step => do
    let tx : Rlp.Transaction1559 := {
      chainId := 1, nonce := i, maxPriorityFeePerGas := 1,
      maxFeePerGas := 3, gas := 1387939, to := some step.to, value := step.value, data := step.data }
    let signed ← checked <| TypedTransaction.sign1559 tx key
    return (tx, signed.transactionHash)
  let statuses := #["confirmed", "confirmed", "confirmed", "confirmed", "confirmed", "planned"]
  let hashes := (transactions.map fun (_, hash) => some hash).push
    (if fault == "planned-hash" then some (bytes 99 32) else none)
  let original ← checked <| DepositMultiSend.journalBytes items .mainnet sender steps statuses hashes
  let original := if fault == "plan" then original ++ "corrupt".toUTF8 else original
  let journal ← IO.mkRef original
  let signs ← IO.mkRef (0 : Nat)
  let sends ← IO.mkRef (0 : Nat)
  let writes ← IO.mkRef (0 : Nat)
  let approved ← IO.mkRef false
  let latest ← IO.mkRef (none : Option (Rlp.Transaction1559 × ByteArray))
  let lookup (params : Array Json) : IO (Rlp.Transaction1559 × ByteArray) := do
    let hash ← checked <| parseHexBytes (← checked params[0]!.getStr?)
    if let some tx := transactions.find? (fun (_, old) => old == hash) then return tx
    let some tx ← latest.get | throw <| IO.userError "Unknown fixture transaction."
    return tx
  let effects : DepositMultiSend.Effects := {
    createJournal := fun _ => throw <| IO.userError "Resume recreated its journal."
    replaceJournal := fun old next => do
      writes.modify (· + 1)
      require ((← journal.get) == old) "Resume overwrote stale bytes."
      if fault == "stale" || (fault == "prepared" && (← signs.get) > 0) then
        throw <| IO.userError "injected CAS failure"
      journal.set next
    approve := fun _ => approved.set true
    waitFinality := fun _ => pure ()
    sign := fun tx => do
      signs.modify (· + 1)
      require ((← approved.get) && tx.nonce == 5 && tx.data == steps[5]!.data && tx.value == pool.amount)
        "Resume signed an already funded or different deposit."
      let signed ← checked <| TypedTransaction.sign1559 tx key
      latest.set (some (tx, signed.transactionHash))
      return (sender, signed)
    rpc := fun identifier method params => do
      match method with
      | .chainId => return toJson ("0x1" : String)
      | .getTransactionCount => return toJson (quantity (5 + (← sends.get) +
          (if (fault == "nonce" && params[1]? == some (toJson ("pending" : String))) ||
            (fault == "late-nonce" && identifier < 700) then 1 else 0)))
      | .blockNumber => return toJson ("0x1" : String)
      | .getBlockByNumber => return Json.mkObj [("number", toJson ("0x1" : String)),
          ("hash", toJson (hex (bytes (if fault == "block" then 18 else 17) 32)))]
      | .getTransactionReceipt =>
        if fault == "pending" then return Json.null
        let (tx, hash) ← lookup params
        return receipt sender tx hash (fault == "event")
      | .getTransactionByHash =>
        let (tx, hash) ← lookup params
        return indexed sender tx hash (fault == "indexed")
      | .call =>
        let request := params[0]!
        let data ← checked <| parseHexBytes (← checked <| (← checked <| request.getObjVal? "data").getStr?)
        if data.extract 0 4 == Abi.selector "commitments(bytes32)" then
          let commitment := data.extract 4 36
          let funded := commitment != steps[5]!.commitment || fault == "funded" ||
            (fault == "after-review" && (← approved.get))
          return toJson (hex (bytes (if funded then 1 else 0) 32))
        let target ← checked <| (← checked <| request.getObjVal? "to").getStr?
        let some selected := items.find? (fun item => item.pool.address.toLower == target.toLower)
          | throw <| IO.userError "Unexpected pool target."
        return toJson (hex (bytes selected.pool.amount 32))
      | .estimateGas => return toJson (quantity 1156615)
      | .feeHistory => return Json.mkObj [("baseFeePerGas", toJson #["0x1", "0x1"]),
          ("reward", toJson #[#["0x1"]])]
      -- Enough for the remaining note, less than the original six-note total.
      | .getBalance => return toJson (quantity (2 * pool.amount))
      | .sendRawTransaction =>
        sends.modify (· + 1)
        let saved ← checked <| DepositStatus.parseJournal ((String.fromUTF8? (← journal.get)).getD "")
        require (saved.steps[5]!.status == .prepared && saved.steps[5]!.hash.isSome)
          "Resumed transaction exposed before durable hash reservation."
        let some (_, hash) ← latest.get | throw <| IO.userError "No signed transaction."
        if fault == "send" then throw <| IO.userError "ambiguous send"
        return toJson (hex hash)
      | _ => throw <| IO.userError "Unexpected resume RPC method." }
  let failure ← try
    let selected := if fault == "reordered" then items.reverse else items
    let chain := if fault == "chain" then ChainId.sepolia else .mainnet
    let owner := if fault == "sender" then sender + 1 else sender
    let _ ← DepositResume.resumeWith effects selected chain owner original
      {maxGas := DepositSend.maxTransactionGas} (!preview)
    pure false
  catch _ => pure true
  if fault.isEmpty then
    require (!failure) "Valid journal resume failed."
    if preview then
      require ((← signs.get) == 0 && (← sends.get) == 0 && (← writes.get) == 0 &&
        (← journal.get) == original) "Resume preview changed state or signed."
    else
      require ((← signs.get) == 1 && (← sends.get) == 1) "Resume did not send exactly the sixth note."
  else if fault == "send" then
    require (failure && (← signs.get) == 1 && (← sends.get) == 1) "Ambiguous resume advanced or retried."
  else if fault == "prepared" then
    require (failure && (← signs.get) == 1 && (← sends.get) == 0) "Failed resumed journal exposed a signature."
  else
    require (failure && (← signs.get) == 0 && (← sends.get) == 0) "Unsafe resume reached signing."
  if fault != "plan" then
    let saved ← checked <| DepositStatus.parseJournal ((String.fromUTF8? (← journal.get)).getD "")
    for i in [0:5] do
      require (saved.steps[i]!.hash == some (hex transactions[i]!.2)) "Resume lost a funded deposit hash."
    if fault == "send" then
      require (saved.steps[5]!.status == .unknown && saved.steps[5]!.hash.isSome)
        "Ambiguous resume lost its exact hash."

def main : IO UInt32 := do
  scenario
  scenario "" true
  scenario "" false true
  scenario "" true true
  for fault in ["plan", "planned-hash", "reordered", "chain", "sender", "pending", "nonce", "late-nonce", "block", "event", "indexed", "funded", "after-review", "stale", "prepared", "send"] do
    scenario fault
  IO.println "PASS: journal-bound five-plus-one resume, read-only preview, exact chain evidence, no replacement, and durable ambiguity"
  return 0
