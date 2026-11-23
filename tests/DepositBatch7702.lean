import Tornado.Cli.DepositBatch7702
import Tornado.Cli.DepositStatusCommand

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Cli
open Tornado.Cli.DepositBatch7702

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def bytes (number count : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [0:count] do
    result := result.push ((number / 256 ^ (count - 1 - i) % 256).toUInt8)
  return result

private def hex := Bundler.dataHex
private def quantity := Bundler.quantity

private def jsonString (json : Json) (key : String) : IO String := do
  checked <| (← checked <| json.getObjVal? key).getStr?

private def jsonNat (json : Json) (key : String) : IO Nat := do
  checked <| JsonRpc.parseHexQuantity (← jsonString json key)

private def decodeOperation (json : Json) (sender : Nat) : IO UserOperation := do
  let factory := (json.getObjVal? "factory").isOk
  let data ← checked <| parseHexBytes (← jsonString json "callData")
  let signature ← checked <| parseHexBytes (← jsonString json "signature")
  return {
    sender, nonce := ← jsonNat json "nonce",
    factory := if factory then some .eip7702Marker else none,
    authorizationAddress := if factory then some implementation else none,
    callData := data, verificationGasLimit := ← jsonNat json "verificationGasLimit",
    callGasLimit := ← jsonNat json "callGasLimit",
    preVerificationGas := ← jsonNat json "preVerificationGas",
    maxFeePerGas := ← jsonNat json "maxFeePerGas",
    maxPriorityFeePerGas := ← jsonNat json "maxPriorityFeePerGas", signature }

private def receipt (sender : Nat) (operation : UserOperation) (hash : ByteArray)
    (chunk : Array DepositMulti.Item) (missingDeposit : Bool) : IO Json := do
  let txHash := bytes 99 32
  let blockHash := bytes 17 32
  let metadata (target : String) (topics : Array String) (data : ByteArray) (index : Nat) :=
    Json.mkObj [("address", toJson target), ("topics", toJson topics),
      ("data", toJson (hex data)), ("transactionHash", toJson (hex txHash)),
      ("blockHash", toJson (hex blockHash)), ("blockNumber", toJson ("0x1" : String)),
      ("transactionIndex", toJson ("0x0" : String)), ("logIndex", toJson (quantity index))]
  let entry := metadata (hex (bytes Bundler.entryPoint 20))
    #[hex Events.userOperationTopic, hex hash, hex (bytes sender 32), hex (bytes 0 32)]
    (bytes operation.nonce 32 ++ bytes 1 32 ++ bytes 1 32 ++ bytes 1 32) 0
  let mut logs := #[entry]
  for i in [0:chunk.size] do
    if missingDeposit && i == 0 then continue
    let item := chunk[i]!
    logs := logs.push (metadata item.pool.address
      #[hex Events.depositTopic, hex item.commitment]
      (bytes i 32 ++ bytes 1 32) (i + 1))
  return Json.mkObj [("transactionHash", toJson (hex txHash)),
    ("blockHash", toJson (hex blockHash)), ("blockNumber", toJson ("0x1" : String)),
    ("transactionIndex", toJson ("0x0" : String)),
    ("from", toJson (hex (bytes 999 20))),
    ("to", toJson (hex (bytes Bundler.entryPoint 20))),
    ("status", toJson ("0x1" : String)), ("logs", Json.arr logs)]

inductive Fault where
  | none | plannedWrite | delegationWrite | preparedWrite | estimate
  | code | fee | cancel | send | hash | receipt | nonceChange | finality | changedKey
  deriving BEq

private def scenario (items : Array DepositMulti.Item) (sender : Nat)
    (code key : ByteArray) (fault : Fault) : IO (Bool × Nat × Nat × Json) := do
  let journal ← IO.mkRef Json.null
  let sends ← IO.mkRef (0 : Nat)
  let signs ← IO.mkRef (0 : Nat)
  let completed ← IO.mkRef (0 : Nat)
  let delegated ← IO.mkRef false
  let reviewed ← IO.mkRef false
  let lastOperation ← IO.mkRef (none : Option UserOperation)
  let lastHash ← IO.mkRef ByteArray.empty
  let chunks ← checked <| DepositMulti.splitItems items (depositBatchLimit items[0]!.pool.asset)
  let effects : Effects := {
    rpc := fun method params => do
      match method with
      | .chainId => return toJson ("0x1" : String)
      | .getCode =>
        let target ← checked <| params[0]!.getStr?
        if target.toLower == (hex (bytes implementation 20)).toLower then
          return toJson (hex (if fault == .code then bytes 1 1 else code))
        return toJson (hex (if (← completed.get) == 0 then ByteArray.empty else designator))
      | .getBalance => return toJson ("0xde0b6b3a7640000" : String)
      | .getTransactionCount =>
        let wasReviewed ← reviewed.get
        let done ← completed.get
        return toJson (quantity (if fault == .nonceChange && wasReviewed then 1 else
          if done == 0 then 0 else 1))
      | .blockNumber => return toJson ("0x1" : String)
      | .call =>
        let request := params[0]!
        let to ← jsonString request "to"
        if to.toLower == (hex (bytes implementation 20)).toLower then
          return toJson (hex (bytes Bundler.entryPoint 32))
        if to.toLower == (hex (bytes Bundler.entryPoint 20)).toLower then
          return toJson (hex (bytes (← completed.get) 32))
        return toJson (hex (bytes items[0]!.pool.amount 32))
      | .feeHistory => return Json.mkObj [
          ("baseFeePerGas", toJson #["0x1", "0x1"]), ("reward", toJson #[#["0x1"]])]
      | .getTransactionReceipt =>
        let some operation ← lastOperation.get
          | throw <| IO.userError "No test UserOperation."
        receipt sender operation (← lastHash.get) chunks[(← sends.get) - 1]!
          (fault == .receipt)
      | _ => throw <| IO.userError "Unexpected test chain method.",
    bundler := fun method params => do
      match method with
      | .pimlicoGasPrice => return Json.mkObj [("standard", Json.mkObj [
          ("maxFeePerGas", toJson (if fault == .fee then "0x2540be400" else "0x3")),
          ("maxPriorityFeePerGas", toJson ("0x1" : String))])]
      | .estimateUserOperationGas =>
        require (← delegated.get) "Estimation ran before explicit delegation approval."
        let stored ← journal.get
        let rows ← checked <| (← checked <| stored.getObjVal? "batches").getArr?
        if (← completed.get) == 0 then
          require ((← jsonString rows[0]! "status") == "unknown")
            "Signed delegation reached estimation before uncertainty was durable."
          let auth ← checked <| rows[0]!.getObjVal? "authorization"
          let sentAuth ← checked <| params[0]!.getObjVal? "eip7702Auth"
          require (auth == sentAuth && (rows[0]!.getObjVal? "authorizationHash").isOk)
            "Signed delegation was not stored exactly before exposure."
        if fault == .estimate then throw <| IO.userError "injected estimator failure"
        return Json.mkObj [("verificationGasLimit", toJson ("0x186a0" : String)),
          ("callGasLimit", toJson ("0x61a80" : String)),
          ("preVerificationGas", toJson ("0xc350" : String))]
      | .sendUserOperation =>
        require (← reviewed.get) "Send occurred before final batch review."
        let operation ← decodeOperation params[0]! sender
        let hash ← checked <| userOperationHash 1 Bundler.entryPoint operation
        let stored ← journal.get
        let rows ← checked <| (← checked <| stored.getObjVal? "batches").getArr?
        require ((← jsonString rows[(← sends.get)]! "status") == "unknown" &&
          (← jsonString rows[(← sends.get)]! "userOpHash") == hex hash)
          "Signed operation was exposed before durable hash reservation."
        lastOperation.set (some operation)
        lastHash.set hash
        sends.modify (· + 1)
        if fault == .send then throw <| IO.userError "injected ambiguous send"
        return toJson (hex (if fault == .hash then bytes 123 32 else hash))
      | .getUserOperationReceipt =>
        let some operation ← lastOperation.get | throw <| IO.userError "No operation."
        return Json.mkObj [("userOpHash", toJson (hex (← lastHash.get))),
          ("entryPoint", toJson (hex (bytes Bundler.entryPoint 20))),
          ("sender", toJson (hex (bytes sender 20))),
          ("nonce", toJson (quantity operation.nonce)), ("success", toJson true),
          ("actualGasCost", toJson ("0x1" : String)), ("actualGasUsed", toJson ("0x1" : String)),
          ("receipt", Json.mkObj [("transactionHash", toJson (hex (bytes 99 32)))])]
      | _ => throw <| IO.userError "Unexpected test bundler method.",
    signDigest := fun digest => do
      require (← delegated.get) "Signing occurred before delegation review."
      signs.modify (· + 1)
      let signature ← checked <| secp256k1SignDigest key digest
      return (if fault == .changedKey then sender + 1 else sender, signature.bytes65),
    createJournal := fun content => do
      if fault == .plannedWrite then throw <| IO.userError "injected initial write failure"
      require ((← journal.get) == .null) "Journal overwritten."
      journal.set (← checked <| Json.parse ((String.fromUTF8? content).getD "")),
    replaceJournal := fun old next => do
      let before ← journal.get
      require (old == (before.compress ++ "\n").toUTF8) "Journal CAS mismatch."
      let after ← checked <| Json.parse ((String.fromUTF8? next).getD "")
      let rows ← checked <| (← checked <| after.getObjVal? "batches").getArr?
      if fault == .delegationWrite && (← signs.get) == 1 then
        throw <| IO.userError "injected delegation journal failure"
      if fault == .preparedWrite && (← signs.get) == 2 then
        throw <| IO.userError "injected signed operation journal failure"
      require (!rows.isEmpty) "Lost journal batches."
      journal.set after,
    approveDelegation := fun _ => delegated.set true,
    approveBatch := fun _ => do
      if fault == .cancel then throw <| IO.userError "injected user cancellation"
      reviewed.set true,
    waitFinality := fun _ => do
      if fault == .finality then throw <| IO.userError "injected finality failure"
      completed.modify (· + 1),
    pause := pure () }
  let passed ← try
    let _ ← executeWith effects items .mainnet sender "https://rpc.invalid" "https://bundler.invalid"
    pure true
  catch _ => pure false
  return (passed, ← sends.get, ← signs.get, ← journal.get)

def main : IO UInt32 := do
  let key := bytes 1 32
  let ownerBytes ← checked <| secp256k1EthereumAddress key
  let sender := ownerBytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let some pool := poolFor .mainnet "0.01" "ETH"
    | throw <| IO.userError "Missing pinned test pool."
  let items : Array DepositMulti.Item := #[⟨pool, bytes 1 32⟩, ⟨pool, bytes 2 32⟩]
  let fixture ← checked <| Json.parse (← IO.FS.readFile "fixtures/simple7702-code.json")
  let code ← checked <| parseHexBytes (← jsonString fixture "code")
  let _ ← checked <| validateImplementation code
  require (!(validateImplementation (bytes 1 1)).isOk) "Changed implementation code was accepted."
  let oracle ← checked <| Json.parse (← IO.FS.readFile "fixtures/deposit7702-vectors.json")
  let poolBytes ← checked <| parseHexBytes pool.address
  let address := poolBytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
  let readings : DepositMulti.Readings :=
    ⟨1, ByteArray.empty, 1000000000000000000, 0, #[⟨address, pool.amount, 0⟩]⟩
  let planned ← checked <| DepositMulti.plan items .mainnet sender
    readings true
  let data ← checked <| callsData planned.batches[0]!
  require (hex data == (← jsonString oracle "callData"))
    "Batched deposit call encoding differs from pinned viem."
  -- Five same-asset notes can require thirteen internal calls: four pools
  -- each reset and approve, followed by five deposits. The public twelve
  -- action cap must not reject this legitimate internal deposit batch.
  let mut daiItems : Array DepositMulti.Item := #[]
  let mut daiPools : Array DepositMulti.PoolReading := #[]
  for (denomination, index) in [("100", 1), ("1000", 2), ("10000", 3), ("100000", 4)] do
    let some daiPool := poolFor .mainnet denomination "DAI"
      | throw <| IO.userError "Missing pinned DAI test pool."
    let poolBytes ← checked <| parseHexBytes daiPool.address
    let poolAddress := poolBytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0
    daiItems := daiItems.push ⟨daiPool, bytes index 32⟩
    daiPools := daiPools.push ⟨poolAddress, daiPool.amount, 1⟩
  daiItems := daiItems.push ⟨daiItems[0]!.pool, bytes 5 32⟩
  let totalDai := daiItems.foldl (fun total item => total + item.pool.amount) 0
  let daiReadings : DepositMulti.Readings :=
    ⟨1, ByteArray.empty, 1000000000000000000, totalDai, daiPools⟩
  let daiPlan ← checked <| DepositMulti.plan daiItems .mainnet sender daiReadings true
  let daiSteps := daiPlan.batches[0]!
  require (daiSteps.size == 13 &&
    (daiSteps.filter (·.kind == .reset)).size == 4 &&
    (daiSteps.filter (·.kind == .approve)).size == 4)
    "Mixed DAI reset/approval fixture did not produce thirteen internal calls."
  let daiData ← checked <| callsData daiSteps
  let countWord := daiData.extract 36 68
  require (daiData.extract 0 4 == Abi.selector "executeBatch((address,uint256,bytes)[])" &&
    countWord == bytes 13 32)
    "Internal deposit encoder changed selector or thirteen-call ABI count."
  let userCalls := daiSteps.map (fun step => (⟨step.to, step.value, step.data⟩ : Abi.ContractCall))
  require (!(Abi.accountExecuteBatch userCalls).isOk)
    "Internal deposit encoder accidentally relaxed the twelve-user-call limit."
  require (!(callsData (Array.replicate 16 daiSteps[0]!)).isOk)
    "Internal deposit encoder exceeded the fifteen-call operational bound."
  let op : UserOperation := {
    sender, nonce := 0, factory := some .eip7702Marker,
    authorizationAddress := some implementation, callData := data,
    verificationGasLimit := 100000, callGasLimit := 400000,
    preVerificationGas := 50000, maxFeePerGas := 3, maxPriorityFeePerGas := 1 }
  let digest ← checked <| userOperationHash 1 Bundler.entryPoint op
  require (hex digest == (← jsonString oracle "userOpHash"))
    "Simple7702 UserOperation hash differs from pinned viem."
  let sig ← checked <| secp256k1SignDigest key digest
  require (hex sig.bytes65 == (← jsonString oracle "signature"))
    "Simple7702 typed-data signature differs from pinned viem."
  let (success, sends, signs, journal) ← scenario items sender code key .none
  require (success && sends == 1 && signs == 2) "Batched deposit did not complete."
  let parsed ← checked <| DepositStatusCommand.parseBatchJournal journal
  require (parsed.batches.size == 1 && parsed.batches[0]!.status == "confirmed")
    "Batch journal is incompatible with native reconciliation."
  let many := (List.range 13).toArray.map (fun i => (⟨pool, bytes (i + 1) 32⟩ : DepositMulti.Item))
  let (multi, multiSends, multiSigns, _) ← scenario many sender code key .none
  require (multi && multiSends == 2 && multiSigns == 3)
    "Multiple batches did not reuse only the current-session delegation."
  for fault in [Fault.plannedWrite, .delegationWrite, .preparedWrite, .estimate,
      .code, .fee, .cancel, .nonceChange, .changedKey] do
    let (passed, sent, _, _) ← scenario items sender code key fault
    require (!passed && sent == 0) "A failed preparation sent a batched operation."
  for fault in [Fault.send, .hash, .receipt, .finality] do
    let (passed, sent, signed, saved) ← scenario many sender code key fault
    require (!passed && sent == 1 && signed == 2)
      "An ambiguous batch advanced to the next signing or send."
    let batches ← checked <| (← checked <| saved.getObjVal? "batches").getArr?
    require ((← jsonString batches[0]! "status") == "unknown" &&
      (← jsonString batches[1]! "status") == "planned")
      "Ambiguous batch lost its reservation or changed the next batch."
  IO.println "PASS: native Simple7702 batches, viem parity, durable delegation exposure, exact events, and ambiguity stop"
  return 0
