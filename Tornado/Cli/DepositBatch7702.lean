import Tornado.Cli.DepositMultiSend
import Tornado.Runtime.Bundler

/-! Simple7702 batched deposits with protected owner signing. Signed
delegation can be executable before an operation is submitted, so the journal
records an uncertain delegation before estimation can expose it. Each batch
is independently reviewed, submitted once, and confirmed from chain events. -/

namespace Tornado.Cli.DepositBatch7702

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Cli.DepositMulti

def implementation : Nat := 0xe6cae83bde06e4c305530e199d7217f42808555b
def implementationHash : String := "0xcc7b633aef4b2543cb8f37522adf1a401f910f0f6b2430c1eecc11f401ccfcf3"

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def hex := Bundler.dataHex
private def quantity := Bundler.quantity
private def address := Bundler.address

private def natOf (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def addr (raw : String) : Except String Nat := do
  if !raw.startsWith "0x" then throw "Invalid deposit address."
  let bytes ← parseHexBytes raw
  if bytes.size != 20 then throw "Invalid deposit address."
  return natOf bytes

def designator : ByteArray :=
  ByteArray.mk #[0xef, 0x01, 0x00] ++
    ((Abi.addressWord implementation).toOption.getD ByteArray.empty).extract 12 32

def validateImplementation (code : ByteArray) : Except String Unit := do
  if code.isEmpty || hex (keccak256 code) != implementationHash then
    throw "Simple7702 implementation differs from the pinned deployed bytecode."

structure Effects where
  rpc : JsonRpc.Method → Array Json → IO Json
  bundler : JsonRpc.Method → Array Json → IO Json
  signDigest : ByteArray → IO (Nat × ByteArray)
  createJournal : ByteArray → IO Unit
  replaceJournal : ByteArray → ByteArray → IO Unit
  approveDelegation : String → IO Unit
  approveBatch : String → IO Unit
  waitFinality : RpcReceipt.Receipt → IO Unit
  pause : IO Unit := IO.sleep 3000

private def rpcQuantity (value : Json) : IO Nat := do
  checked <| JsonRpc.parseHexQuantity (← checked value.getStr?)

private def rpcBytes (value : Json) (maxBytes : Nat) : IO ByteArray := do
  let text ← checked value.getStr?
  if !text.startsWith "0x" || text.utf8ByteSize > 2 * maxBytes + 2 then
    throw <| IO.userError "RPC byte string exceeds the supported bound."
  checked <| parseHexBytes text

private def callWord (effects : Effects) (target : Nat) (data : ByteArray) : IO Nat := do
  let result ← effects.rpc .call #[Json.mkObj [
    ("to", toJson (← checked <| address target)), ("data", toJson (hex data))],
    toJson ("latest" : String)]
  let bytes ← rpcBytes result 32
  if bytes.size != 32 then throw <| IO.userError "Contract did not return one uint256 word."
  return natOf bytes

private def codeAt (effects : Effects) (target : Nat) : IO ByteArray := do
  rpcBytes (← effects.rpc .getCode
    #[toJson (← checked <| address target), toJson ("latest" : String)]) 65536

private def checkCode (effects : Effects) (sender : Nat) (first : Bool) : IO Unit := do
  let code ← codeAt effects sender
  if (if first then !code.isEmpty else code != designator) then
    throw <| IO.userError "Sender code or delegation changed; stop before another deposit."
  let _ ← checked <| validateImplementation (← codeAt effects implementation)
  let actualEntryPoint ← callWord effects implementation (Abi.selector "entryPoint()")
  if actualEntryPoint != Bundler.entryPoint then
    throw <| IO.userError "Simple7702 implementation uses an unexpected EntryPoint."

private def readingsWith (effects : Effects) (items : Array Item)
    (chain : ChainId) (sender : Nat) : IO Readings := do
  if items.isEmpty then throw <| IO.userError "No selected deposit notes."
  let senderText ← checked <| address sender
  let actualChain ← rpcQuantity (← effects.rpc .chainId #[])
  if actualChain != chainNumber chain then throw <| IO.userError "RPC is on a different network."
  let code ← codeAt effects sender
  let balance ← rpcQuantity (← effects.rpc .getBalance
    #[toJson senderText, toJson ("pending" : String)])
  let mut tokenBalance := 0
  if let some tokenText := items[0]!.pool.asset.token then
    tokenBalance ← callWord effects (← checked <| addr tokenText)
      (Abi.selector "balanceOf(address)" ++ (← checked <| Abi.addressWord sender))
  let mut pools : Array PoolReading := #[]
  for item in items do
    let pool ← checked <| addr item.pool.address
    if pools.any (fun p => p.address == pool) then continue
    let denomination ← callWord effects pool (Abi.selector "denomination()")
    let mut allowance := 0
    if let some tokenText := item.pool.asset.token then
      allowance ← callWord effects (← checked <| addr tokenText)
        (Abi.selector "allowance(address,address)" ++
          (← checked <| Abi.addressWord sender) ++ (← checked <| Abi.addressWord pool))
    pools := pools.push ⟨pool, denomination, allowance⟩
  return ⟨actualChain, code, balance, tokenBalance, pools⟩

def callsData (steps : Array Tornado.Cli.DepositSend.Step) : Except String ByteArray := do
  -- At most five ERC-20 deposits, each with reset+approve, or twelve ETH
  -- deposits. These internal calls are distinct from the twelve user calls
  -- allowed by the public action importer.
  if steps.isEmpty || steps.size > 15 then throw "Invalid batched deposit call count."
  let calls := steps.map (fun step => (⟨step.to, step.value, step.data⟩ : Abi.ContractCall))
  if calls.size == 1 then
    let call := calls[0]!
    Abi.accountExecute call.to call.value call.data
  else Abi.accountExecuteBatchComposed calls

private def nonce (effects : Effects) (sender : Nat) (tag : String) : IO Nat := do
  rpcQuantity (← effects.rpc .getTransactionCount
    #[toJson (← checked <| address sender), toJson tag])

private def entryNonce (effects : Effects) (sender : Nat) : IO Nat := do
  callWord effects Bundler.entryPoint (Abi.selector "getNonce(address,uint192)" ++
    (← checked <| Abi.addressWord sender) ++ (← checked <| Abi.uintWord 0))

private def checkedSignature (effects : Effects) (sender : Nat)
    (digest : ByteArray) : IO ByteArray := do
  let (actual, signature) ← effects.signDigest digest
  if actual != sender || signature.size != 65 ||
      (signature[64]! != 27 && signature[64]! != 28) then
    throw <| IO.userError "Signing key or signature differs from reviewed owner."
  let r := natOf (signature.extract 0 32)
  let s := natOf (signature.extract 32 64)
  if r == 0 || r >= secp256k1Order || s == 0 || s > secp256k1Order / 2 then
    throw <| IO.userError "Noncanonical owner signature."
  return signature

private def fees (effects : Effects) (custom : Bool) : IO (Nat × Nat) := do
  let history ← effects.rpc .feeHistory #[toJson ("0x1" : String),
    toJson ("latest" : String), toJson (#[50] : Array Nat)]
  let bases ← checked <| (← checked <| history.getObjVal? "baseFeePerGas").getArr?
  let rewards ← checked <| (← checked <| history.getObjVal? "reward").getArr?
  if bases.size != 2 || rewards.size != 1 then throw <| IO.userError "Invalid bounded fee history."
  let reward ← checked rewards[0]!.getArr?
  if reward.size != 1 then throw <| IO.userError "Invalid bounded fee reward."
  let base ← rpcQuantity bases[1]!
  let priority ← rpcQuantity reward[0]!
  let reference := 2 * base + priority
  if reference == 0 || reference > 1000000000000 then
    throw <| IO.userError "Chain fee reference exceeds the supported bound."
  if custom then return (2 * priority, 2 * reference)
  let quoted ← effects.bundler .pimlicoGasPrice #[]
  if quoted.compress.utf8ByteSize > 16384 then throw <| IO.userError "Oversized bundler fee quote."
  let standard ← checked <| quoted.getObjVal? "standard"
  let maximum ← rpcQuantity (← checked <| standard.getObjVal? "maxFeePerGas")
  let tip ← rpcQuantity (← checked <| standard.getObjVal? "maxPriorityFeePerGas")
  if maximum == 0 || tip > maximum || maximum > 4 * reference + 1000000000 ||
      tip > 4 * (priority + 1000000000) then
    throw <| IO.userError "Bundler fees exceed the bounded live-chain reference."
  return (tip, maximum)

private def recordBytes (items : Array Item) : Json := Json.arr <| items.map fun item =>
  Json.mkObj [("pool", toJson item.pool.address),
    ("commitment", toJson (hex item.commitment)),
    ("denomination", toJson item.pool.denomination), ("asset", toJson item.pool.asset.symbol)]

def initialJournal (chunks : Array (Array Item)) (chain : ChainId)
    (sender : Nat) (rpcUrl bundlerUrl : String) : Except String Json := do
  return Json.mkObj [("version", toJson (1 : Nat)),
    ("kind", toJson ("deposit-7702-batch" : String)),
    ("chainId", toJson (chainNumber chain)), ("sender", toJson (← address sender)),
    ("entryPointAddress", toJson (← address Bundler.entryPoint)),
    ("implementation", toJson (← address implementation)),
    ("rpcUrl", toJson rpcUrl), ("bundlerUrl", toJson bundlerUrl),
    ("createdAt", toJson ("native-lean" : String)),
    ("batches", Json.arr (chunks.map fun chunk => Json.mkObj [
      ("status", toJson ("planned" : String)), ("deposits", recordBytes chunk)]))]

private def journalBytes (json : Json) : ByteArray := (json.compress ++ "\n").toUTF8

private def awaitBatch (effects : Effects) (operation : UserOperation)
    (hash : ByteArray) (chunk : Array Item) : IO RpcReceipt.Receipt := do
  let expected : Events.ExpectedEntry :=
    ⟨Bundler.entryPoint, hash, operation.sender, 0, operation.nonce⟩
  let mut deposits := []
  for item in chunk do
    deposits := deposits ++ [⟨← checked <| addr item.pool.address, item.commitment⟩]
  for _ in [0:60] do
    let hint ← effects.bundler .getUserOperationReceipt #[toJson (hex hash)]
    if hint != .null then
      let envelope := Json.mkObj [("jsonrpc", toJson ("2.0" : String)),
        ("id", toJson (1 : Nat)), ("result", hint)]
      let some parsed ← checked <| RpcReceipt.parseBundlerResponse envelope 1 expected
        | throw <| IO.userError "Missing bundler receipt hint."
      let chainReceipt ← effects.rpc .getTransactionReceipt #[toJson (hex parsed.transactionHash)]
      if chainReceipt != .null then
        let receipt ← checked <| RpcReceipt.parseReceipt chainReceipt parsed.transactionHash
        match RpcReceipt.batchDepositOutcome receipt parsed.transactionHash expected deposits none with
        | .confirmed => return receipt
        | .failed => throw <| IO.userError "The batch failed on chain; delegation may remain."
        | .unknown => throw <| IO.userError "Chain receipt does not prove every selected deposit."
    effects.pause
  throw <| IO.userError "Batch remains unconfirmed; do not submit more deposits."

def executeWith (effects : Effects) (items : Array Item) (chain : ChainId)
    (sender : Nat) (rpcUrl bundlerUrl : String) (customBundler : Bool := false)
    (bounds : Bundler.Bounds := {}) : IO String := do
  let readings ← readingsWith effects items chain sender
  let planned ← checked <| DepositMulti.plan items chain sender readings false
  if planned.mode != .simple7702 then
    throw <| IO.userError "This deposit selection uses the sequential transaction route."
  checkCode effects sender true
  let chunks ← checked <| splitItems items (depositBatchLimit items[0]!.pool.asset)
  let initial ← checked <| initialJournal chunks chain sender rpcUrl bundlerUrl
  let journal ← IO.mkRef initial
  effects.createJournal (journalBytes initial)
  let update (index : Nat) (fields : List (String × Json)) : IO Unit := do
    let prior ← journal.get
    let batches ← checked <| (← checked <| prior.getObjVal? "batches").getArr?
    let mut batch := batches[index]!
    for (key, value) in fields do batch := batch.setObjVal! key value
    let next := prior.setObjVal! "batches" (.arr (batches.set! index batch))
    effects.replaceJournal (journalBytes prior) (journalBytes next)
    journal.set next
  for index in [0:chunks.size] do
    let first := index == 0
    let chunk := chunks[index]!
    checkCode effects sender first
    let current ← readingsWith effects chunk chain sender
    let sequence ← checked <| DepositMulti.plan chunk chain sender current true
    let steps := sequence.batches[0]!
    let data ← checked <| callsData steps
    let accountNonce ← entryNonce effects sender
    let (priority, maximum) ← fees effects customBundler
    let mut authorization : Option Bundler.Authorization := none
    if first then
      let pending ← nonce effects sender "pending"
      if pending >= 2 ^ 64 - 1 || pending != (← nonce effects sender "latest") then
        throw <| IO.userError "Pending or unprocessable owner nonce; refusing delegation."
      effects.approveDelegation s!"Authorize persistent Simple7702 delegation of {← checked <| address sender} to {← checked <| address implementation} on chain {chainNumber chain}. The signed authorization reaches bundler estimation and can be relayed even if the deposit is cancelled."
      checkCode effects sender true
      if pending != (← nonce effects sender "pending") || pending != (← nonce effects sender "latest") then
        throw <| IO.userError "Owner nonce changed after delegation review."
      let digest ← checked <| Rlp.authorizationHash7702 (chainNumber chain) implementation pending
      let signature ← checkedSignature effects sender digest
      let signed : Bundler.Authorization := {
        chainId := chainNumber chain, delegate := implementation, nonce := pending,
        r := natOf (signature.extract 0 32), s := natOf (signature.extract 32 64),
        yParity := signature[64]!.toNat - 27 }
      authorization := some signed
      -- Store uncertainty before any signed delegation can reach estimation.
      update index [("status", toJson ("unknown" : String)),
        ("authorization", ← checked <| Bundler.authorizationJson signed),
        ("authorizationHash", toJson (hex digest)),
        ("message", toJson ("A signed 7702 authorization may reach estimation; inspect delegation before retrying." : String))]
    let stub ← checked <| parseHexBytes "0xfffffffffffffffffffffffffffffff0000000000000000000000000000000007aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa1c"
    let baseline : UserOperation := {
      sender, nonce := accountNonce,
      factory := if first then some .eip7702Marker else none,
      authorizationAddress := if first then some implementation else none,
      callData := data, verificationGasLimit := 300000,
      callGasLimit := 4000000, preVerificationGas := 100000,
      maxPriorityFeePerGas := priority, maxFeePerGas := maximum,
      signature := stub }
    let estimateRequest ← checked <| Bundler.withAuthorization (chainNumber chain) baseline authorization
    let estimate ← effects.bundler .estimateUserOperationGas
      #[estimateRequest, toJson (← checked <| address Bundler.entryPoint)]
    let gas ← checked <| Bundler.parseEstimate estimate baseline bounds
    let operation := { baseline with
      verificationGasLimit := gas.verificationGasLimit,
      callGasLimit := gas.callGasLimit, preVerificationGas := gas.preVerificationGas }
    let _ ← checked <| Bundler.validate operation bounds
    let cost := Bundler.maximumGasCost operation
    let amount := chunk.foldl (fun sum item => sum + item.pool.amount) 0
    if !chunk[0]!.pool.asset.token.isSome && cost > amount / 10 then
      throw <| IO.userError "Batch maximum network fee exceeds ten percent of ETH deposits."
    let senderBalance ← rpcQuantity (← effects.rpc .getBalance
      #[toJson (← checked <| address sender), toJson ("pending" : String)])
    if senderBalance < cost + (if chunk[0]!.pool.asset.token.isSome then 0 else amount) then
      throw <| IO.userError "Sender lacks the deposit amount and maximum network fee."
    let hash ← checked <| userOperationHash (chainNumber chain) Bundler.entryPoint operation
    let fromBlock ← rpcQuantity (← effects.rpc .blockNumber #[])
    effects.approveBatch s!"Batch {index + 1}/{chunks.size}: {chunk.size} deposit(s), {steps.size} ordered calls, amount {amount} base units, maximum gas cost {cost} wei, UserOperation {hex hash}, calldata {hex data}."
    -- Re-plan after asynchronous user approval so a changed token allowance
    -- cannot change the calls that will actually be signed.
    checkCode effects sender first
    let afterRead ← readingsWith effects chunk chain sender
    let afterPlan ← checked <| DepositMulti.plan chunk chain sender afterRead true
    if (← checked <| callsData afterPlan.batches[0]!) != data ||
        (← entryNonce effects sender) != accountNonce ||
        afterRead.ethBalance < cost + (if chunk[0]!.pool.asset.token.isSome then 0 else amount) then
      throw <| IO.userError "Calls or account nonce changed after batch review."
    if let some auth := authorization then
      if (← nonce effects sender "pending") != auth.nonce ||
          (← nonce effects sender "latest") != auth.nonce then
        throw <| IO.userError "Owner nonce changed after batch review."
    let signature ← checkedSignature effects sender hash
    let finalOperation := { operation with signature := signature }
    let bundlerEffects : Bundler.Effects := {
      rpc := effects.bundler,
      reserve := fun known _ => update index [
        ("status", toJson ("prepared" : String)), ("userOpHash", toJson (hex known)),
        ("nonce", toJson (quantity accountNonce)), ("fromBlock", toJson (quantity fromBlock))],
      markExposed := fun _ => update index [("status", toJson ("unknown" : String))],
      markSubmitted := fun _ => update index [("status", toJson ("submitted" : String))],
      markUnknown := fun _ => update index [("status", toJson ("unknown" : String))] }
    match ← Bundler.submitWith bundlerEffects (chainNumber chain) finalOperation bounds authorization with
    | .unknown known => throw <| IO.userError s!"Batch outcome unknown for {hex known}; reconcile before another send."
    | .submitted _ => pure ()
    try
      let receipt ← awaitBatch effects finalOperation hash chunk
      effects.waitFinality receipt
      update index [("status", toJson ("confirmed" : String)),
        ("transactionHash", toJson (hex receipt.transactionHash)), ("message", .null)]
    catch _ =>
      try update index [("status", toJson ("unknown" : String))] catch _ => pure ()
      throw <| IO.userError s!"Batch {hex hash} needs reconciliation; remaining deposits were stopped."
  return s!"Confirmed {items.size} deposit(s) in {chunks.size} Simple7702 batch(es). Delegation persists."

private def absolutePath (path : String) : IO String := do
  let current ← IO.currentDir
  return if (System.FilePath.mk path).isAbsolute then path else (current / path).toString

/-- Live adapter for explicitly selected experimental batching. It shares
the sender lock and permanent invoice claims with sequential native sends. -/
def experimentalSend (notesFile keyFile rpcUrl bundlerUrl journalPath : String)
    (chain : ChainId) (customBundler : Bool := false) (yes : Bool := false) : IO String := do
  let keyPath ← absolutePath keyFile
  let sender ← NativeSigner.addressFromProtectedFile keyPath
  let senderText ← checked <| address sender
  let privateBytes ← ProtectedIO.readPrivate (← absolutePath notesFile)
  let some text := String.fromUTF8? privateBytes
    | throw <| IO.userError "Private note backup is not UTF-8."
  let items ← checked <| DepositMulti.publicItems text chain
  let readings ← DepositMulti.liveReadings rpcUrl items chain sender
  let plan ← checked <| DepositMulti.plan items chain sender readings false
  if plan.mode != .simple7702 then
    throw <| IO.userError "This selection requires the sequential transaction route."
  let journalPath ← absolutePath journalPath
  let keyDirectory := String.intercalate "/" (keyPath.splitOn "/").dropLast
  if keyDirectory.isEmpty then throw <| IO.userError "Key file has no safe parent directory."
  let lockPath := keyDirectory ++ "/.tornado-sender-" ++
    toString (chainNumber chain) ++ "-" ++ senderText.toLower ++ ".lock"
  let lockBytes := ((Json.mkObj [("version", toJson (1 : Nat)),
    ("kind", toJson ("sender-lock" : String)), ("sender", toJson senderText),
    ("journal", toJson journalPath)]).compress ++ "\n").toUTF8
  ProtectedIO.createPrivate lockPath lockBytes
  let created ← IO.mkRef (#[] : Array (String × ByteArray))
  try
    for item in items do
      let identity := s!"tornado-lean-cli/invoice/v1/{chainNumber chain}/{item.pool.address.toLower}/{(hex item.commitment).toLower}"
      let claimPath := keyDirectory ++ "/.tornado-invoice-" ++
        bytesToHex (keccak256 identity.toUTF8) ++ ".claim"
      let content := ((Json.mkObj [("version", toJson (1 : Nat)),
        ("kind", toJson ("invoice-claim" : String)),
        ("chainId", toJson (chainNumber chain)), ("pool", toJson item.pool.address),
        ("commitment", toJson (hex item.commitment)),
        ("sender", toJson senderText), ("journal", toJson journalPath)]).compress ++ "\n").toUTF8
      ProtectedIO.createPrivate claimPath content
      created.modify (·.push (claimPath, content))
  catch error =>
    for (path, content) in (← created.get) do
      try ProtectedIO.removePrivateExact path content catch _ => pure ()
    try ProtectedIO.removePrivateExact lockPath lockBytes catch _ => pure ()
    throw error
  let nextId ← IO.mkRef (1 : Nat)
  let fetch (url : String) (method : JsonRpc.Method) (params : Array Json) : IO Json := do
    let id ← nextId.get
    nextId.set (id + 1)
    HttpTransport.call url id method params
  let effects : Effects := {
    rpc := fetch rpcUrl, bundler := fetch bundlerUrl,
    signDigest := NativeSigner.signDigest65FromProtectedFile keyPath,
    createJournal := ProtectedIO.createPrivate journalPath,
    replaceJournal := ProtectedIO.replacePrivate journalPath,
    waitFinality := ProtectedTxSender.waitReceiptDepth rpcUrl,
    approveDelegation := fun review => do
      IO.println review
      IO.println "Type DELEGATE to authorize persistent EIP-7702 delegation:"
      if jsTrim (← (← IO.getStdin).getLine) != "DELEGATE" then
        throw <| IO.userError "Delegation cancelled before signing.",
    approveBatch := fun review => do
      IO.println review
      if !yes then
        IO.println "Type SEND to sign and submit this one batch:"
        if jsTrim (← (← IO.getStdin).getLine) != "SEND" then
          throw <| IO.userError "Batch cancelled before signing." }
  let result ← try executeWith effects items chain sender rpcUrl bundlerUrl customBundler
    catch _ =>
      throw <| IO.userError s!"Batched deposit stopped. Inspect {journalPath} and sender delegation; lock remains at {lockPath}. Do not retry until all signed candidates and delegation are reconciled."
  ProtectedIO.removePrivateExact lockPath lockBytes
  return result

/-- Match the pinned CLI's automatic route choice. Existing sender code,
a single deposit without approval, or an explicit sequential preference use
ordinary transactions; an undelegated EOA with a multi-call plan uses 7702. -/
def experimentalAutoSend (notesFile keyFile rpcUrl bundlerUrl journalPath : String)
    (chain : ChainId) (forceSequential customBundler yes : Bool) : IO String := do
  let keyPath ← absolutePath keyFile
  let sender ← NativeSigner.addressFromProtectedFile keyPath
  let bytes ← ProtectedIO.readPrivate (← absolutePath notesFile)
  let some text := String.fromUTF8? bytes
    | throw <| IO.userError "Private note backup is not UTF-8."
  let items ← checked <| DepositMulti.publicItems text chain
  let readings ← DepositMulti.liveReadings rpcUrl items chain sender
  let selected ← checked <| DepositMulti.plan items chain sender readings forceSequential
  match selected.mode with
  | .sequential =>
    Tornado.Cli.DepositMultiSend.experimentalSend notesFile keyFile rpcUrl journalPath chain yes
  | .simple7702 =>
    experimentalSend notesFile keyFile rpcUrl bundlerUrl journalPath chain customBundler yes

end Tornado.Cli.DepositBatch7702
