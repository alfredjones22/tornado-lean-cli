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
  | code | senderCodeChange | senderCodeOnReplan | codeAfterDelegationReview
  | fee | cancel | send | hash | receipt
  | nonceChange | initialNonceMismatch | finality | changedKey
  deriving BEq

private def scenario (items : Array DepositMulti.Item) (sender : Nat)
    (code key : ByteArray) (fault : Fault)
    (initialSenderCode : ByteArray := ByteArray.empty)
    (forceDelegated : Bool := false)
    (estimateCallGas : Nat := 400000)
    (estimateVerificationGas : Nat := 100000)
    (estimatePreVerificationGas : Nat := 50000)
    (feeBase : Nat := 1) (priorityFee : Nat := 1)
    (quotedMaxFee : Option Nat := none)
    (expectedFailure : Option String := none)
    (gasCredit : Nat := 0) (walletBalance : Option Nat := none)
    (afterReviewGasCredit : Option Nat := none)
    (afterReviewBalance : Option Nat := none)
    (malformedCredit : Option String := none)
    (afterReviewMalformedCredit : Option String := none)
    (failCreditReadAfterConfirmation : Bool := false)
    (expectedSummary : Option String := none) :
    IO (Bool × Nat × Nat × Json × Bool) := do
  let journal ← IO.mkRef Json.null
  let sends ← IO.mkRef (0 : Nat)
  let signs ← IO.mkRef (0 : Nat)
  let completed ← IO.mkRef (0 : Nat)
  let delegated ← IO.mkRef false
  let reviewed ← IO.mkRef false
  let postReviewSenderCodeReads ← IO.mkRef (0 : Nat)
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
        let wasReviewed ← reviewed.get
        let wasDelegated ← delegated.get
        let done ← completed.get
        let afterReviewReads ← if wasReviewed then do
          postReviewSenderCodeReads.modify (· + 1)
          postReviewSenderCodeReads.get
        else pure 0
        return toJson (hex (if fault == .senderCodeChange && wasReviewed then bytes 1 1
          else if fault == .senderCodeOnReplan && afterReviewReads >= 2 then bytes 1 1
          else if fault == .codeAfterDelegationReview && wasDelegated then bytes 1 1
          else if done == 0 then initialSenderCode else designator))
      | .getBalance =>
        let initial := walletBalance.getD 1000000000000000000
        return toJson (quantity (if ← reviewed.get then
          afterReviewBalance.getD initial else initial))
      | .getTransactionCount =>
        let wasReviewed ← reviewed.get
        let done ← completed.get
        let tag ← checked <| params[1]!.getStr?
        return toJson (quantity (if fault == .initialNonceMismatch && tag == "pending" then 1 else
          if fault == .nonceChange && wasReviewed then 1 else
          if done == 0 then 0 else 1))
      | .blockNumber => return toJson ("0x1" : String)
      | .call =>
        let request := params[0]!
        let to ← jsonString request "to"
        if to.toLower == (hex (bytes implementation 20)).toLower then
          return toJson (hex (bytes Bundler.entryPoint 32))
        if to.toLower == (hex (bytes Bundler.entryPoint 20)).toLower then
          let data ← jsonString request "data"
          if data == hex (Abi.selector "balanceOf(address)" ++
              (← checked <| Abi.addressWord sender)) then
            if failCreditReadAfterConfirmation && (← completed.get) > 0 then
              throw <| IO.userError "injected post-confirmation gas-credit read failure"
            let malformed := if ← reviewed.get then
              afterReviewMalformedCredit.orElse (fun _ => malformedCredit) else malformedCredit
            if let some malformed := malformed then return toJson malformed
            let credit := if ← reviewed.get then afterReviewGasCredit.getD gasCredit
              else gasCredit
            return toJson (hex (bytes credit 32))
          return toJson (hex (bytes (← completed.get) 32))
        return toJson (hex (bytes items[0]!.pool.amount 32))
      | .feeHistory => return Json.mkObj [
          ("baseFeePerGas", toJson (#[quantity feeBase, quantity feeBase])),
          ("reward", toJson (#[#[quantity priorityFee]]))]
      | .getTransactionReceipt =>
        let some operation ← lastOperation.get
          | throw <| IO.userError "No test UserOperation."
        receipt sender operation (← lastHash.get) chunks[(← sends.get) - 1]!
          (fault == .receipt)
      | _ => throw <| IO.userError "Unexpected test chain method.",
    bundler := fun method params => do
      match method with
      | .pimlicoGasPrice => return Json.mkObj [("standard", Json.mkObj [
          ("maxFeePerGas", toJson (quantity <| quotedMaxFee.getD
            (if fault == .fee then 10000000000 else 3))),
          ("maxPriorityFeePerGas", toJson (quantity priorityFee))])]
      | .estimateUserOperationGas =>
        let stored ← journal.get
        let rows ← checked <| (← checked <| stored.getObjVal? "batches").getArr?
        if (← completed.get) == 0 then
          if initialSenderCode == designator then
            require (!(← delegated.get) &&
              (← jsonString rows[0]! "status") == "planned" &&
              !(rows[0]!.getObjVal? "authorization").isOk &&
              !(params[0]!.getObjVal? "eip7702Auth").isOk &&
              !(params[0]!.getObjVal? "factory").isOk)
              "Compatible delegation reuse sent a new authorization or factory marker."
          else
            require (← delegated.get) "Estimation ran before explicit delegation approval."
            require ((← jsonString rows[0]! "status") == "unknown")
              "Signed delegation reached estimation before uncertainty was durable."
            let auth ← checked <| rows[0]!.getObjVal? "authorization"
            let sentAuth ← checked <| params[0]!.getObjVal? "eip7702Auth"
            require (auth == sentAuth && (rows[0]!.getObjVal? "authorizationHash").isOk)
              "Signed delegation was not stored exactly before exposure."
        else
          require (!(params[0]!.getObjVal? "eip7702Auth").isOk &&
            !(params[0]!.getObjVal? "factory").isOk)
            "A later batch carried a second authorization or factory marker."
        if fault == .estimate then throw <| IO.userError "injected estimator failure"
        return Json.mkObj [("verificationGasLimit", toJson (quantity estimateVerificationGas)),
          ("callGasLimit", toJson (quantity estimateCallGas)),
          ("preVerificationGas", toJson (quantity estimatePreVerificationGas))]
      | .sendUserOperation =>
        require (← reviewed.get) "Send occurred before final batch review."
        let operation ← decodeOperation params[0]! sender
        if (← sends.get) == 0 && initialSenderCode == designator then
          require (operation.factory.isNone &&
            !(params[0]!.getObjVal? "eip7702Auth").isOk)
            "Compatible delegation reuse sent a factory marker or new authorization."
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
      signs.modify (· + 1)
      require ((← delegated.get) || (← reviewed.get))
        "Signing occurred before delegation or batch review."
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
      if fault == .preparedWrite && (← jsonString rows[0]! "status") == "prepared" then
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
    let result ← executeWith effects items .mainnet sender "https://rpc.invalid" "https://bundler.invalid"
      false defaultBounds forceDelegated
    if let some expected := expectedSummary then
      require ((result.splitOn expected).length > 1)
        "Confirmed deposit omitted the expected gas-credit summary."
    pure true
  catch error =>
    if let some expected := expectedFailure then
      require ((error.toString.splitOn expected).length > 1)
        s!"Expected {expected}, got {error}."
    pure false
  return (passed, ← sends.get, ← signs.get, ← journal.get, ← delegated.get)

set_option maxRecDepth 4096 in
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
  let (success, sends, signs, journal, approved) ← scenario items sender code key .none
  require (success && sends == 1 && signs == 2 && approved)
    "Batched deposit did not durably authorize and complete."
  let parsed ← checked <| DepositStatusCommand.parseBatchJournal journal
  require (parsed.batches.size == 1 && parsed.batches[0]!.status == "confirmed")
    "Batch journal is incompatible with native reconciliation."
  let many := (List.range 13).toArray.map (fun i => (⟨pool, bytes (i + 1) 32⟩ : DepositMulti.Item))
  let (multi, multiSends, multiSigns, _, _) ← scenario many sender code key .none
  require (multi && multiSends == 2 && multiSigns == 3)
    "Multiple batches did not reuse only the current-session delegation."
  let (reuse, reuseSends, reuseSigns, reusedJournal, reuseApproved) ←
    scenario items sender code key .none designator
  require (reuse && reuseSends == 1 && reuseSigns == 1 && !reuseApproved)
    "Compatible existing delegation signed a new authorization or missed its batch."
  require (requiredNativeBalance 1000 100 20 == 1080 &&
    requiredNativeBalance 1000 100 100 == 1000 &&
    requiredNativeBalance 1000 100 200 == 1000 &&
    requiredNativeBalance 0 100 200 == 0)
    "EntryPoint gas credit funded principal or underflowed the required native balance."
  let totalValue := items.foldl (fun total item => total + item.pool.amount) 0
  let maximumCost := (400000 + 100000 + 50000) * 3
  let (creditFull, creditFullSends, creditFullSigns, _, _) ←
    scenario items sender code key .none designator
      (gasCredit := maximumCost) (walletBalance := some totalValue)
      (expectedSummary := some "Remaining EntryPoint gas credit:")
  require (creditFull && creditFullSends == 1 && creditFullSigns == 1)
    "Fully funded EntryPoint credit did not permit exact ETH principal in the wallet."
  let (creditPartial, creditPartialSends, _, _, _) ←
    scenario items sender code key .none designator
      (gasCredit := maximumCost - 1) (walletBalance := some (totalValue + 1))
  require (creditPartial && creditPartialSends == 1)
    "Partial EntryPoint credit was ignored when checking native gas funding."
  let some creditTokenPool := poolFor .mainnet "100" "USDC"
    | throw <| IO.userError "Missing token gas-credit fixture pool."
  let creditTokenItems : Array DepositMulti.Item := #[⟨creditTokenPool, bytes 777 32⟩]
  let (tokenCredit, tokenCreditSends, tokenCreditSigns, _, _) ←
    scenario creditTokenItems sender code key .none designator true
      (gasCredit := maximumCost) (walletBalance := some 0)
  require (tokenCredit && tokenCreditSends == 1 && tokenCreditSigns == 1)
    "Fully credited token deposit incorrectly required ETH in the owner wallet."
  let (creditInsufficient, creditInsufficientSends, creditInsufficientSigns, _, _) ←
    scenario items sender code key .none designator
      (gasCredit := maximumCost - 2) (walletBalance := some (totalValue + 1))
  require (!creditInsufficient && creditInsufficientSends == 0 && creditInsufficientSigns == 0)
    "Insufficient combined wallet/EntryPoint gas funding reached signing."
  let (principalMissing, principalMissingSends, principalMissingSigns, _, _) ←
    scenario items sender code key .none designator
      (gasCredit := maximumCost * 2) (walletBalance := some (totalValue - 1))
  require (!principalMissing && principalMissingSends == 0 && principalMissingSigns == 0)
    "EntryPoint gas credit was counted toward the ETH deposit principal."
  for changedCredit in [0, maximumCost - 2] do
    let (changed, changedSends, changedSigns, _, _) ←
      scenario items sender code key .none designator
        (gasCredit := maximumCost) (walletBalance := some (totalValue + 1))
        (afterReviewGasCredit := some changedCredit)
    require (!changed && changedSends == 0 && changedSigns == 0)
      "Gas credit lost after approval was not rechecked before signing."
  let (balanceLost, balanceLostSends, balanceLostSigns, _, _) ←
    scenario items sender code key .none designator
      (gasCredit := maximumCost - 1) (walletBalance := some (totalValue + 1))
      (afterReviewBalance := some totalValue)
  require (!balanceLost && balanceLostSends == 0 && balanceLostSigns == 0)
    "Native gas funding lost after approval was not rechecked before signing."
  for malformed in ["0x", hex (bytes 1 31), hex (bytes 1 33), "0xzz"] do
    let (accepted, sent, signed, _, _) ← scenario items sender code key .none designator
      (malformedCredit := some malformed)
    require (!accepted && sent == 0 && signed == 0)
      "Malformed EntryPoint gas credit reached signing or submission."
  let (malformedAfter, malformedAfterSends, malformedAfterSigns, _, _) ←
    scenario items sender code key .none designator
      (gasCredit := maximumCost) (walletBalance := some totalValue)
      (afterReviewMalformedCredit := some "0x01")
  require (!malformedAfter && malformedAfterSends == 0 && malformedAfterSigns == 0)
    "Malformed gas credit after approval reached signing or submission."
  let (creditReadFailed, creditReadFailedSends, _, _, _) ←
    scenario items sender code key .none designator
      (failCreditReadAfterConfirmation := true)
      (expectedSummary := some "the deposits remain confirmed")
  require (creditReadFailed && creditReadFailedSends == 1)
    "Optional credit reporting turned a confirmed deposit into a failure."
  let reuseRows ← checked <| (← checked <| reusedJournal.getObjVal? "batches").getArr?
  require ((← jsonString reuseRows[0]! "status") == "confirmed" &&
    !(reuseRows[0]!.getObjVal? "authorization").isOk &&
    (← jsonString reusedJournal "initialSenderCode") == hex designator &&
    (← checked <| (← checked <| reusedJournal.getObjVal? "reusedDelegation").getBool?))
    "Compatible delegation reuse journal unexpectedly included an authorization."
  let (reuseMany, reuseManySends, reuseManySigns, _, reuseManyApproved) ←
    scenario many sender code key .none designator
  require (reuseMany && reuseManySends == 2 && reuseManySigns == 2 && !reuseManyApproved)
    "Compatible delegation was not safely reused across multiple batches."
  let twelve := (List.range 12).toArray.map fun i =>
    (⟨pool, bytes (i + 1) 32⟩ : DepositMulti.Item)
  let (large, largeSends, largeSigns, _, largeApproved) ←
    scenario twelve sender code key .none designator false
      13879390 100000 50000 0 1000000000 (some 1000000000)
  let twelveCost := (13879390 + 100000 + 50000) * 1000000000
  require (twelveCost > 12 * pool.amount / 10 &&
    twelveCost < 50000000000000000 &&
    large && largeSends == 1 && largeSigns == 1 && !largeApproved)
    "Twelve small notes at 1 gwei were blocked by the old aggregate 10% cap."
  let some largerPool := poolFor .mainnet "0.1" "ETH"
    | throw <| IO.userError "Missing larger ETH fixture pool."
  let largerItem : DepositMulti.Item := ⟨largerPool, bytes 40 32⟩
  let (largerAccepted, largerSends, largerSigns, _, _) ←
    scenario #[largerItem] sender code key .none designator true
      1000000 100000 50000 7000000000 1000000000 (some 15000000000)
      (some "Batch maximum network fee exceeds ten percent of ETH deposits.")
  let largerCost := (1000000 + 100000 + 50000) * 15000000000
  require (largerCost > largerPool.amount / 10 &&
    largerCost < 50000000000000000 &&
    !largerAccepted && largerSends == 0 && largerSigns == 0)
    "A batch with a note above 0.01 ETH bypassed the retained 10% cap."
  let (absoluteAccepted, absoluteSends, absoluteSigns, _, _) ←
    scenario twelve sender code key .none designator false
      13879390 100000 50000 1500000000 1000000000 (some 4000000000)
      (some "UserOperation exceeds the reviewed gas or network fee bounds.")
  require ((13879390 + 100000 + 50000) * 4000000000 >
    50000000000000000 && 13879390 < defaultBounds.maxCallGas &&
    13879390 + 100000 + 50000 < maxOperationGas &&
    !absoluteAccepted && absoluteSends == 0 && absoluteSigns == 0)
    "All-small batch bypassed the retained 0.05 ETH absolute fee cap."
  let (excessive, excessiveSends, excessiveSigns, _, _) ←
    scenario twelve sender code key .none designator false 15000001
  require (!excessive && excessiveSends == 0 && excessiveSigns == 0)
    "Call gas above the deposit-only 15m cap reached signing or submission."
  let (combined, combinedSends, combinedSigns, _, _) ←
    scenario twelve sender code key .none designator false 14900000 900000 500000
  require (!combined && combinedSends == 0 && combinedSigns == 0)
    "UserOperation over the 16m combined gas cap reached signing or submission."
  let foreign := bytes 0xef 1 ++ bytes 0x01 1 ++ bytes 0 1 ++ bytes 123 20
  let (replaced, replacedSends, replacedSigns, _, replaceApproved) ←
    scenario items sender code key .none foreign true
  require (replaced && replacedSends == 1 && replacedSigns == 2 && replaceApproved)
    "Forced replacement of an existing 7702 designator did not authorize once."
  let (changedForeign, changedForeignSends, changedForeignSigns, _, _) ←
    scenario items sender code key .codeAfterDelegationReview foreign true
  require (!changedForeign && changedForeignSends == 0 && changedForeignSigns == 0)
    "Sender code changed after delegation review but authorization was signed."
  let (plainForeign, plainForeignSends, plainForeignSigns, _, _) ←
    scenario items sender code key .none foreign
  require (!plainForeign && plainForeignSends == 0 && plainForeignSigns == 0)
    "Foreign 7702 designator entered the batch route without --delegated."
  let (forcedOne, forcedOneSends, forcedOneSigns, _, forcedOneApproved) ←
    scenario #[items[0]!] sender code key .none ByteArray.empty true
  require (forcedOne && forcedOneSends == 1 && forcedOneSigns == 2 && forcedOneApproved)
    "Explicit delegation did not batch a single approval-free note."
  let (reuseOne, reuseOneSends, reuseOneSigns, _, reuseOneApproved) ←
    scenario #[items[0]!] sender code key .none designator
  require (!reuseOne && reuseOneSends == 0 && reuseOneSigns == 0 && !reuseOneApproved)
    "Compatible delegation enabled an implicit single-note UserOperation."
  let (forcedReuseOne, forcedReuseOneSends, forcedReuseOneSigns, _, forcedReuseOneApproved) ←
    scenario #[items[0]!] sender code key .none designator true
  require (forcedReuseOne && forcedReuseOneSends == 1 && forcedReuseOneSigns == 1 && !forcedReuseOneApproved)
    "--delegated failed to reuse a compatible delegation for one note."
  for invalid in [bytes 0x60 1, foreign.extract 0 22] do
    let (passed, sent, signed, _, _) ← scenario items sender code key .none invalid true
    require (!passed && sent == 0 && signed == 0)
      "Forced delegation accepted ordinary contract or malformed 7702 code."
  for fault in [Fault.senderCodeChange, .initialNonceMismatch] do
    let (passed, sent, signed, _, _) ← scenario items sender code key fault designator
    require (!passed && sent == 0 && signed == 0)
      "Compatible delegation signed or sent after changed code or owner nonce."
  let (changedOnReplan, replanSends, replanSigns, _, _) ←
    scenario items sender code key .senderCodeOnReplan designator
  require (!changedOnReplan && replanSends == 0 && replanSigns == 0)
    "Fresh sender code changed during replan but UserOperation was signed or sent."
  let (reservation, reservedSends, reservedSigns, reservationJournal, _) ←
    scenario items sender code key .preparedWrite designator
  let reservationRows ← checked <| (← checked <| reservationJournal.getObjVal? "batches").getArr?
  require (!reservation && reservedSends == 0 && reservedSigns == 1 &&
    (← jsonString reservationRows[0]! "status") == "planned" &&
    !(reservationRows[0]!.getObjVal? "userOpHash").isOk)
    "Failed reused-delegation hash reservation exposed or saved a signed operation."
  for fault in [Fault.send, .hash] do
    let (passed, sent, signed, saved, approved) ←
      scenario many sender code key fault designator
    let batches ← checked <| (← checked <| saved.getObjVal? "batches").getArr?
    require (!passed && sent == 1 && signed == 1 && !approved &&
      (← jsonString batches[0]! "status") == "unknown" &&
      (← jsonString batches[1]! "status") == "planned" &&
      (← jsonString batches[0]! "userOpHash").utf8ByteSize == 66)
      "Ambiguous reused-delegation batch lost its hash or advanced to a second send."
  for fault in [Fault.plannedWrite, .delegationWrite, .preparedWrite, .estimate,
      .code, .fee, .cancel, .nonceChange, .changedKey] do
    let (passed, sent, _, _, _) ← scenario items sender code key fault
    require (!passed && sent == 0) "A failed preparation sent a batched operation."
  for fault in [Fault.send, .hash, .receipt, .finality] do
    let (passed, sent, signed, saved, _) ← scenario many sender code key fault
    require (!passed && sent == 1 && signed == 2)
      "An ambiguous batch advanced to the next signing or send."
    let batches ← checked <| (← checked <| saved.getObjVal? "batches").getArr?
    require ((← jsonString batches[0]! "status") == "unknown" &&
      (← jsonString batches[1]! "status") == "planned" &&
      (← jsonString batches[0]! "userOpHash").utf8ByteSize == 66)
      "Ambiguous batch lost its reservation or changed the next batch."
  IO.println "PASS: native Simple7702 batches, viem parity, durable delegation exposure, exact events, and ambiguity stop"
  return 0
