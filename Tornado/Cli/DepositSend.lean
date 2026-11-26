import Tornado.Runtime.WithdrawalJournalProgram
import Lean
import Tornado.Domain.DepositBackup
import Tornado.Protocol.Abi
import Tornado.Protocol.RpcReceipt
import Tornado.Protocol.TypedTransaction
import Tornado.Protocol.TypedTransactionDecode
import Tornado.Protocol.DepositIntent
import Tornado.Runtime.HttpTransport
import Tornado.Runtime.NativeSigner
import Tornado.Runtime.ProtectedIO
import Tornado.Runtime.ProtectedTxSender
import Tornado.Cli.PrivateKeyInput

/-!
Selected-pool sequential deposit engine. Planning, signing, journal writes,
network exposure, and receipt reconciliation remain visibly separate. The
live invoice route signs through a protected native secp256k1 boundary and
exposes only public signature data to Lean. It still requires the explicitly
experimental CLI flag and per-transaction typed confirmation; the full
funded path is not certified. A public-invoice dry run is available. No note
preimage is placed in calls or journal records.
-/

namespace Tornado.Cli.DepositSend

open Lean Tornado.Domain Tornado.Protocol Tornado.Crypto Tornado.Runtime

inductive DepositFileKind where
  | senderLock | invoiceClaim | journal

/-- Keep exclusive creation and existing reservations intact; only translate
    a structured already-exists failure into deposit-specific recovery advice. -/
def createProtectedFile (kind : DepositFileKind) (path : String)
    (contents : ByteArray) : IO Unit := do
  try WithdrawalJournalProgram.createProtected path contents
  catch error =>
    match error with
    | .alreadyExists _ _ _ =>
      let message := match kind with
        | .senderLock =>
          "A deposit sender lock already exists: " ++ path ++
          "\nA previous attempt may be pending or unfinished. Inspect its original journal with deposit status. For a sequential ETH plan, continue with the original notes and journal using deposit send --resume. Reconcile every recorded hash before removing this lock."
        | .invoiceClaim =>
          "A deposit reservation already exists for this note commitment: " ++ path ++
          "\nClaims normally remain after a successful deposit to prevent funding the same commitment twice. Inspect the original journal with deposit status; use deposit send --resume for an unfinished sequential ETH plan. Do not delete Tornado dotfiles just to bypass the reservation."
        | .journal =>
          "A deposit journal already exists: " ++ path ++
          "\nKeep the original journal. For a sequential ETH plan, rerun deposit send with the same notes and journal plus --resume. Other routes require reconciliation before another attempt."
      throw <| IO.userError message
    | _ => throw error

/-- Classic pool deposits can need more than one million gas. Allow a bounded
    two million including estimation headroom; fee-cost caps remain separate. -/
def maxTransactionGas : Nat := 2000000

/-- Small deposits can cost more than ten percent of their denomination to
    execute. Keep the absolute fee ceiling for them and approvals. -/
def valueGasDivisor (value : Nat) : Nat :=
  if value ≤ 10000000000000000 then 0 else 10

/-- The native deposit fee ceiling: 0.02 ETH, with an additional ten-percent
    limit only when the value is greater than 0.01 ETH. -/
def gasCostLimit (value : Nat) : Nat :=
  if valueGasDivisor value == 0 then 20000000000000000
  else min 20000000000000000 (value / 10)

/-- Adapt the ordinary default relative limit per deposit. Stricter custom
    relative divisors and lower absolute caller ceilings remain effective. -/
def stepBounds (bounds : ProtectedTxSender.Bounds) (value : Nat) : ProtectedTxSender.Bounds :=
  { bounds with
    maxGasCostWei := min bounds.maxGasCostWei 20000000000000000
    valueGasDivisor := if value > 0 && valueGasDivisor value == 0 &&
      bounds.valueGasDivisor == 10 then 0 else bounds.valueGasDivisor }

inductive StepKind where
  | reset | approve | deposit
  deriving Repr, BEq, DecidableEq, Inhabited

def StepKind.text : StepKind → String
  | .reset => "reset"
  | .approve => "approve"
  | .deposit => "deposit"

structure Step where
  kind : StepKind
  label : String
  to : Nat
  data : ByteArray
  value : Nat
  pool : Nat := 0
  commitment : ByteArray := ByteArray.empty
  spender : Nat := 0
  approvalAmount : Nat := 0
  deriving Inhabited

/-- Copy the actual executable and journal fields without re-encoding data. -/
def stepEncoding (step : Step) : DepositIntent.EncodedStep := {
  kind := match step.kind with
    | .reset => .reset | .approve => .approve | .deposit => .deposit
  to := step.to, value := step.value, data := step.data, pool := step.pool,
  commitment := step.commitment, spender := step.spender, approvalAmount := step.approvalAmount }

structure Readings where
  chainId : Nat
  denomination : Nat
  ethBalance : Nat
  tokenBalance : Nat := 0
  allowance : Nat := 0
  deriving Inhabited

private def addressNat (raw : String) : Except String Nat := do
  if !raw.startsWith "0x" then throw "Expected a 20-byte Ethereum address."
  let bytes ← parseHexBytes raw
  if bytes.size != 20 then throw "Expected a 20-byte Ethereum address."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def addressText (value : Nat) : Except String String := do
  if value == 0 || value >= 2 ^ 160 then throw "Invalid deposit address."
  let word ← Abi.addressWord value
  return "0x" ++ bytesToHex (word.extract 12 32)

private def fixedHex (bytes : ByteArray) : String := "0x" ++ bytesToHex bytes

private def depositStep (pool : Pool) (commitment : ByteArray)
    (poolAddress : Nat) : Except String Step := do
  let data ← Abi.poolDeposit commitment
  return ⟨.deposit, s!"Deposit {pool.denomination} {pool.asset.symbol}",
    poolAddress, data, if pool.asset.token.isSome then 0 else pool.amount,
    poolAddress, commitment, 0, 0⟩

/-- Pure invoice planner. All chain readings are supplied by the caller and
    must be independently obtained from the selected RPC before use. -/
private def planInvoiceCandidate (invoice : PublicInvoice) (sender : Nat)
    (readings : Readings) : Except String (Array Step) := do
  let pool := invoice.pool
  if sender == 0 || sender >= 2 ^ 160 ||
      readings.chainId != chainNumber pool.chainId ||
      readings.denomination != pool.amount then
    throw "Invoice pool, network, or on-chain denomination does not match."
  let some known := poolFor pool.chainId pool.denomination pool.asset.symbol
    | throw "Invoice pool is unavailable in the pinned catalog."
  if known != pool then throw "Invoice pool differs from the pinned catalog."
  let poolAddress ← addressNat pool.address
  let commitment ← parseHexBytes invoice.commitment
  if commitment.size != 32 || invoice.call.to != pool.address ||
      invoice.call.value != (if pool.asset.token.isSome then 0 else pool.amount) ||
      invoice.call.data != fixedHex (← Abi.poolDeposit commitment) then
    throw "Invoice commitment or deposit calldata differs from reviewed pool."
  let mut steps := #[]
  if let some tokenText := pool.asset.token then
    let token ← addressNat tokenText
    if readings.tokenBalance < pool.amount || readings.ethBalance == 0 then
      throw "Deposit sender lacks the selected token or ETH gas balance."
    if readings.allowance < pool.amount then
      if readings.allowance > 0 then
        steps := steps.push ⟨.reset, s!"Reset {pool.asset.symbol} approval",
          token, (← Abi.erc20Approve poolAddress 0), 0, 0,
          ByteArray.empty, poolAddress, 0⟩
      steps := steps.push ⟨.approve,
        s!"Approve exactly {pool.amount} base units of {pool.asset.symbol}",
        token, (← Abi.erc20Approve poolAddress pool.amount), 0, 0,
        ByteArray.empty, poolAddress, pool.amount⟩
  else if readings.ethBalance <= pool.amount then
    throw "Deposit sender needs the selected ETH plus gas."
  steps := steps.push (← depositStep pool commitment poolAddress)
  return steps

/-- An invoice payer receives only a public commitment and pool. This intent
does not require or retain a spendable note or any note preimage. -/
def invoiceIntent (invoice : PublicInvoice) (sender : Nat) (readings : Readings) :
    Except String DepositIntent.Input := do
  let pool ← addressNat invoice.pool.address
  let token : Option Nat ← match invoice.pool.asset.token with
    | none => pure none
    | some text => some <$> addressNat text
  let commitment ← parseHexBytes invoice.commitment
  return {
    items := #[{ pool, token, denomination := invoice.pool.amount, commitment := commitment.data }],
    sender, chainId := chainNumber invoice.pool.chainId, actualChainId := readings.chainId,
    senderCode := #[], ethBalance := readings.ethBalance, tokenBalance := readings.tokenBalance,
    pools := #[{ address := pool, denomination := readings.denomination, allowance := readings.allowance }],
    forceSequential := true, limit := depositBatchLimit invoice.pool.asset }

structure PreparedInvoice (invoice : PublicInvoice) (sender : Nat) (readings : Readings) where
  private mk ::
  steps : Array Step
  input : DepositIntent.Input
  original : invoiceIntent invoice sender readings = .ok input
  checked : DepositIntent.CheckedSteps input (steps.map stepEncoding)

def prepareInvoice (invoice : PublicInvoice) (sender : Nat) (readings : Readings) :
    Except String (PreparedInvoice invoice sender readings) :=
  match planInvoiceCandidate invoice sender readings with
  | .error error => .error error
  | .ok steps =>
    match original : invoiceIntent invoice sender readings with
    | .error error => .error error
    | .ok input =>
      match DepositIntent.acceptSteps input (steps.map stepEncoding) with
      | .error error => .error error
      | .ok checked => .ok ⟨steps, input, original, checked⟩

/-- Actual public planning succeeds only with independently decoded deposit
and approval fields equal to the original invoice and reading snapshot. -/
def planInvoice (invoice : PublicInvoice) (sender : Nat)
    (readings : Readings) : Except String (Array Step) :=
  (prepareInvoice invoice sender readings).map (·.steps)

theorem planInvoice_success_decodes (invoice : PublicInvoice) (sender : Nat) (readings : Readings)
    (steps : Array Step) (built : planInvoice invoice sender readings = .ok steps) :
    ∃ input meaning, invoiceIntent invoice sender readings = .ok input ∧
      DepositIntent.expected input = .ok meaning ∧ meaning.mode = .sequential ∧
      meaning.batches.size = 1 ∧
      DepositIntent.decodeSteps (steps.map stepEncoding) = .ok meaning.batches[0]! ∧
      DepositIntent.PlanPolicy input meaning := by
  cases prepared : prepareInvoice invoice sender readings with
  | error error => simp [planInvoice, prepared, Except.map] at built
  | ok result =>
    have same : result.steps = steps := by simpa [planInvoice, prepared, Except.map] using built
    subst steps
    exact ⟨result.input, result.checked.meaning, result.original, result.checked.original,
      result.checked.sequential, result.checked.singleBatch, result.checked.decoded, result.checked.policy⟩

private def fromExcept (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw <| IO.userError message

private def rpcCall (rpc : String) (id : Nat) (method : JsonRpc.Method)
    (params : Array Json) : IO Json :=
  HttpTransport.call rpc id method params

private def rpcQuantity (value : Json) : IO Nat := do
  let raw ← fromExcept value.getStr?
  fromExcept <| JsonRpc.parseHexQuantity raw

private def rpcWord (value : Json) : IO Nat := do
  let raw ← fromExcept value.getStr?
  let bytes ← fromExcept <| parseHexBytes raw
  if !raw.startsWith "0x" || bytes.size != 32 then
    throw <| IO.userError "RPC contract call did not return one uint256 word."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def callData (to : Nat) (data : ByteArray) : IO (Array Json) := do
  let target ← fromExcept <| addressText to
  return #[Json.mkObj [("to", toJson target), ("data", toJson (fixedHex data))],
    toJson ("latest" : String)]

private def readContractWord (rpc : String) (id target : Nat)
    (data : ByteArray) : IO Nat := do
  let result ← rpcCall rpc id .call (← callData target data)
  rpcWord result

private def absolutePrivatePath (path : String) : IO String := do
  let current ← IO.currentDir
  return if (System.FilePath.mk path).isAbsolute then path
    else (current / path).toString

/-- The file must be mode 0600 and contain only a 32-byte hex key, with
    optional surrounding whitespace. The key is never accepted from argv. -/
def readKey (path : String) : IO ByteArray := do
  let rawBytes ← ProtectedIO.readPrivate (← absolutePrivatePath path)
  fromExcept <| PrivateKeyInput.parse rawBytes

/-- Derive the public payer address without importing the key into Lean. -/
private def senderFromKeyFile (path : String) : IO Nat := do
  NativeSigner.addressFromProtectedFile (← absolutePrivatePath path)

private def readInvoice (path : String) (chain : ChainId) : IO PublicInvoice := do
  let content ← IO.FS.readFile path
  if content.utf8ByteSize > 1024 then
    throw <| IO.userError "Public invoice file is too large."
  fromExcept <| parseInvoice content chain

/-- Live RPC reads for the selected invoice. No signature or broadcast. -/
def readInvoicePlan (rpc : String) (invoice : PublicInvoice)
    (sender : Nat) : IO (Readings × Array Step) := do
  let pool := invoice.pool
  let poolAddress ← fromExcept <| addressNat pool.address
  let senderText ← fromExcept <| addressText sender
  let chainId ← rpcQuantity (← rpcCall rpc 1 .chainId #[])
  if chainId != chainNumber pool.chainId then
    throw <| IO.userError "RPC endpoint is on a different chain."
  let denomination ← readContractWord rpc 2 poolAddress
    (Abi.selector "denomination()")
  let ethBalance ← rpcQuantity (← rpcCall rpc 3 .getBalance
    #[toJson senderText, toJson ("pending" : String)])
  let mut tokenBalance := 0
  let mut allowance := 0
  if let some tokenText := pool.asset.token then
    let token ← fromExcept <| addressNat tokenText
    tokenBalance ← readContractWord rpc 4 token
      (Abi.selector "balanceOf(address)" ++ (← fromExcept <| Abi.addressWord sender))
    allowance ← readContractWord rpc 5 token
      (Abi.selector "allowance(address,address)" ++
        (← fromExcept <| Abi.addressWord sender) ++
        (← fromExcept <| Abi.addressWord poolAddress))
  let readings := { chainId, denomination, ethBalance, tokenBalance, allowance : Readings }
  let steps ← fromExcept <| planInvoice invoice sender readings
  return (readings, steps)

private def renderStep (index : Nat) (step : Step) : IO String := do
  let target ← fromExcept <| addressText step.to
  return s!"  {index + 1}. {step.label}; to {target}; value {step.value} wei; data {fixedHex step.data}"

/-- Runnable public-invoice review. It reads a protected key to derive the
    sender, checks the live chain, denomination, balances and allowance, and
    prints exact calls without signing or creating a journal. -/
def dryRunPayInvoice (invoiceFile keyFile rpc : String)
    (chain : ChainId) : IO String := do
  let sender ← senderFromKeyFile keyFile
  let invoice ← readInvoice invoiceFile chain
  let (_, steps) ← readInvoicePlan rpc invoice sender
  let senderText ← fromExcept <| addressText sender
  let mut lines := #[s!"Sender: {senderText}",
    s!"Invoice: {invoice.raw}",
    s!"Total: {invoice.pool.denomination} {invoice.pool.asset.symbol}",
    "Route: sequential EIP-1559 transactions."]
  for i in [0:steps.size] do
    lines := lines.push (← renderStep i steps[i]!)
  lines := lines.push "Dry run complete. No transaction was signed or submitted."
  return String.intercalate "\n" lines.toList

inductive StepStatus where
  | planned | prepared | submitted | confirmed | reverted
  deriving Repr, BEq, Inhabited

def StepStatus.text : StepStatus → String
  | .planned => "planned"
  | .prepared => "prepared"
  | .submitted => "submitted"
  | .confirmed => "confirmed"
  | .reverted => "reverted"

private def quantityText (value : Nat) : String := Id.run do
  if value == 0 then return "0x0"
  let alphabet := "0123456789abcdef".toList.toArray
  let mut remaining := value
  let mut digits := ""
  while remaining > 0 do
    digits := String.singleton alphabet[remaining % 16]! ++ digits
    remaining := remaining / 16
  return "0x" ++ digits

private def journalBytes (invoice : PublicInvoice) (sender : Nat)
    (steps : Array Step) (statuses : Array StepStatus)
    (hashes : Array (Option ByteArray)) : Except String ByteArray := do
  if steps.size != statuses.size || steps.size != hashes.size ||
      steps.isEmpty || steps.size > 3 then
    throw "Invalid sequential deposit journal dimensions."
  let mut items := #[]
  for i in [0:steps.size] do
    let step := steps[i]!
    let mut fields := [
      ("kind", toJson step.kind.text),
      ("label", toJson step.label),
      ("to", toJson (← addressText step.to)),
      ("status", toJson statuses[i]!.text)]
    if let some hash := hashes[i]! then
      if hash.size != 32 then throw "Invalid prepared transaction hash."
      fields := fields ++ [("hash", toJson (fixedHex hash))]
    if step.kind == .deposit then
      fields := fields ++ [
        ("pool", toJson (← addressText step.pool)),
        ("commitment", toJson (fixedHex step.commitment)),
        ("denomination", toJson invoice.pool.denomination),
        ("asset", toJson invoice.pool.asset.symbol)]
    items := items.push (Json.mkObj fields)
  return ((Json.mkObj [
    ("version", toJson (1 : Nat)), ("kind", toJson ("deposit" : String)),
    ("chainId", toJson (chainNumber invoice.pool.chainId)),
    ("account", toJson (← addressText sender)),
    ("createdAt", toJson ("native-lean" : String)),
    ("steps", Json.arr items)]).compress ++ "\n").toUTF8

/-- All effects are injected so a fault test can prove that a failed journal
    write prevents broadcast, and that an unknown broadcast stops the run. -/
structure Effects where
  rpc : Nat → JsonRpc.Method → Array Json → IO Json
  createJournal : ByteArray → IO Unit
  replaceJournal : ByteArray → ByteArray → IO Unit
  sign : Rlp.Transaction1559 → IO (Nat × TypedTransaction.SignedTyped)
  approve : String → IO Unit
  waitFinality : RpcReceipt.Receipt → IO Unit

private def rpcWordWith (effects : Effects) (id target : Nat)
    (data : ByteArray) : IO Nat := do
  rpcWord (← effects.rpc id .call (← callData target data))

private def feeQuote (effects : Effects) (id : Nat) : IO (Nat × Nat) := do
  let result ← effects.rpc id .feeHistory
    #[toJson ("0x1" : String), toJson ("latest" : String),
      toJson (#[50] : Array Nat)]
  let bases ← fromExcept <| (← fromExcept <| result.getObjVal? "baseFeePerGas").getArr?
  if bases.size != 2 then throw <| IO.userError "Fee history has no next-block base fee."
  let base ← rpcQuantity bases[1]!
  let rewards ← fromExcept <| (← fromExcept <| result.getObjVal? "reward").getArr?
  if rewards.size != 1 then throw <| IO.userError "Fee history has no priority fee quote."
  let reward ← fromExcept <| rewards[0]!.getArr?
  if reward.size != 1 then throw <| IO.userError "Fee history has no priority fee percentile."
  let priority ← rpcQuantity reward[0]!
  let maxFee := 2 * base + priority
  if maxFee == 0 || maxFee >= 2 ^ 256 then
    throw <| IO.userError "RPC EIP-1559 fee quote is invalid."
  return (priority, maxFee)

private def txMatches (requested actual : Rlp.Transaction1559) : Bool :=
  requested.chainId == actual.chainId && requested.nonce == actual.nonce &&
  requested.maxPriorityFeePerGas == actual.maxPriorityFeePerGas &&
  requested.maxFeePerGas == actual.maxFeePerGas &&
  requested.gas == actual.gas && requested.to == actual.to &&
  requested.value == actual.value && requested.data == actual.data &&
  actual.accessList.isEmpty

private def signedMatches (tx : Rlp.Transaction1559)
    (signed : TypedTransaction.SignedTyped) : Except String Unit := do
  if signed.transactionHash != keccak256 signed.serialized ||
      signed.signingHash != (← Rlp.signingHash1559 tx) ||
      (← Rlp.serialize1559 tx (some signed.signature)) != signed.serialized then
    throw "Signed transaction bytes differ from the reviewed EIP-1559 call."
  let decoded ← TypedTransactionDecode.decode1559 signed.serialized
  if decoded.signature.isNone || !txMatches tx decoded.tx then
    throw "Signed transaction fields differ from the reviewed EIP-1559 call."

/-- The actual invoice signer uses this gate before returning signed bytes
for journaling. It keeps existing hash/serialization checks and additionally
certifies the independently decoded executable deposit or approval step. -/
def certifySignedStep (step : Step) (tx : Rlp.Transaction1559)
    (signed : TypedTransaction.SignedTyped) :
    Except String (DepositIntent.CheckedSignedStep (stepEncoding step) tx signed.serialized) := do
  signedMatches tx signed
  DepositIntent.acceptSignedStep (stepEncoding step) tx signed.serialized

theorem certifySignedStep_success_decodes (step : Step) (tx : Rlp.Transaction1559)
    (signed : TypedTransaction.SignedTyped)
    (success : (certifySignedStep step tx signed).isOk = true) :
    ∃ actual : TypedTransactionDecode.Canonical1559 signed.serialized,
      TypedTransactionDecode.decode1559 signed.serialized = .ok actual ∧
      actual.signature.isSome = true ∧ DepositIntent.TransactionMatches tx actual.tx ∧
      DepositIntent.StepMatches (stepEncoding step) tx ∧
      ∃ meaning, DepositIntent.decodeStep (stepEncoding step) = .ok meaning ∧
        DepositIntent.decodeStep (DepositIntent.executableStep (stepEncoding step) actual.tx) = .ok meaning := by
  cases accepted : certifySignedStep step tx signed with
  | error error => simp [accepted, Except.isOk, Except.toBool] at success
  | ok checked => exact DepositIntent.checked_signed_step (stepEncoding step) tx signed.serialized checked

/-- The signing effect returns the public address of the key used. Reject a
    changed key or malformed signed transaction before journaling exposure. -/
private def signWithReviewedSender (effects : Effects) (sender : Nat)
    (step : Step) (tx : Rlp.Transaction1559) :
    IO TypedTransaction.SignedTyped := do
  let (actualSender, signed) ← effects.sign tx
  if actualSender != sender then
    throw <| IO.userError "Private key does not match the reviewed sender."
  let _ ← fromExcept <| certifySignedStep step tx signed
  return signed

private def transactionFor (effects : Effects) (chainId sender : Nat)
    (step : Step) (index : Nat) : IO Rlp.Transaction1559 := do
  let baseId := 100 + index * 20
  let senderText ← fromExcept <| addressText sender
  let targetText ← fromExcept <| addressText step.to
  let nonce ← rpcQuantity (← effects.rpc baseId .getTransactionCount
    #[toJson senderText, toJson ("pending" : String)])
  let minedNonce ← rpcQuantity (← effects.rpc (baseId + 4) .getTransactionCount
    #[toJson senderText, toJson ("latest" : String)])
  if nonce != minedNonce then
    throw <| IO.userError "Sender has a pending transaction; native deposit will not risk replacing it."
  let call := Json.mkObj [
    ("from", toJson senderText), ("to", toJson targetText),
    ("data", toJson (fixedHex step.data)),
    ("value", toJson (quantityText step.value))]
  let estimate ← rpcQuantity (← effects.rpc (baseId + 1) .estimateGas #[call])
  let gas := estimate * 120 / 100 + 1
  if estimate == 0 || gas > maxTransactionGas then
    throw <| IO.userError s!"RPC gas estimate {estimate} (buffered: {gas}) is zero or exceeds the native limit of {maxTransactionGas}."
  let (priority, maxFee) ← feeQuote effects (baseId + 2)
  let maxGasCost := gas * maxFee
  if maxGasCost > gasCostLimit step.value then
    throw <| IO.userError "The quoted maximum gas cost exceeds the safety cap."
  let balance ← rpcQuantity (← effects.rpc (baseId + 3) .getBalance
    #[toJson senderText, toJson ("pending" : String)])
  if balance < step.value + maxGasCost then
    throw <| IO.userError "Sender lacks ETH for the deposit value and reviewed maximum gas cost."
  let tx : Rlp.Transaction1559 :=
    { chainId, nonce, maxPriorityFeePerGas := priority,
      maxFeePerGas := maxFee, gas, to := some step.to,
      value := step.value, data := step.data }
  let _ ← fromExcept <| Rlp.validateTransaction tx
  return tx

private def recheckTokenDeposit (effects : Effects) (invoice : PublicInvoice)
    (sender : Nat) (step : Step) (id : Nat) : IO Unit := do
  if step.kind != .deposit then return
  if let some tokenText := invoice.pool.asset.token then
    let token ← fromExcept <| addressNat tokenText
    let balance ← rpcWordWith effects id token
      (Abi.selector "balanceOf(address)" ++ (← fromExcept <| Abi.addressWord sender))
    let allowance ← rpcWordWith effects (id + 1) token
      (Abi.selector "allowance(address,address)" ++
        (← fromExcept <| Abi.addressWord sender) ++
        (← fromExcept <| Abi.addressWord step.pool))
    if balance < invoice.pool.amount || allowance < invoice.pool.amount then
      throw <| IO.userError "Token balance or allowance changed before deposit."

private def confirmedReceipt (effects : Effects) (hash : ByteArray)
    (id : Nat) : IO RpcReceipt.Receipt := do
  for attempt in [0:90] do
    let result ← effects.rpc (id + attempt) .getTransactionReceipt #[toJson (fixedHex hash)]
    if result != Json.null then
      return (← fromExcept <| RpcReceipt.parseReceipt result hash)
    if attempt < 89 then IO.sleep 2000
  throw <| IO.userError s!"Transaction {fixedHex hash} is still unconfirmed; reconcile before another send."

/-- The effectful sequential engine. It validates the invoice/plan, creates a
    protected planned journal, signs one reviewed tx, durably records its exact
    hash, broadcasts once, and only then seeks exact receipt/event evidence.
    Any failure or ambiguity stops before signing a later step. -/
def executeWith (effects : Effects) (invoice : PublicInvoice) (sender : Nat)
    (readings : Readings) : IO String := do
  let steps ← fromExcept <| planInvoice invoice sender readings
  let mut statuses := Array.replicate steps.size StepStatus.planned
  let mut hashes := Array.replicate steps.size (none : Option ByteArray)
  let mut journal ← fromExcept <| journalBytes invoice sender steps statuses hashes
  effects.createJournal journal
  for i in [0:steps.size] do
    let step := steps[i]!
    recheckTokenDeposit effects invoice sender step (200 + i * 20)
    let tx ← transactionFor effects (chainNumber invoice.pool.chainId) sender step i
    let targetText ← fromExcept <| addressText step.to
    effects.approve s!"Step {i + 1}/{steps.size}: {step.label}; target {targetText}; value {tx.value} wei; calldata {fixedHex tx.data}; nonce {tx.nonce}; gas {tx.gas}; max fee {tx.maxFeePerGas} wei/gas; maximum gas cost {tx.gas * tx.maxFeePerGas} wei ({formatUnitsExact (tx.gas * tx.maxFeePerGas) 18} ETH)."
    let signed ← signWithReviewedSender effects sender step tx
    hashes := hashes.set! i (some signed.transactionHash)
    statuses := statuses.set! i .prepared
    let prepared ← fromExcept <| journalBytes invoice sender steps statuses hashes
    effects.replaceJournal journal prepared
    journal := prepared
    let returned ← try
      effects.rpc (300 + i * 20) .sendRawTransaction
        #[toJson (fixedHex signed.serialized)]
    catch _ =>
      throw <| IO.userError s!"Broadcast outcome unknown for {fixedHex signed.transactionHash}; reconcile before another send."
    let responseHash ← fromExcept <| parseHexBytes (← fromExcept returned.getStr?)
    if responseHash != signed.transactionHash then
      throw <| IO.userError s!"RPC returned a different transaction hash; reconcile {fixedHex signed.transactionHash}."
    statuses := statuses.set! i .submitted
    let submitted ← fromExcept <| journalBytes invoice sender steps statuses hashes
    effects.replaceJournal journal submitted
    journal := submitted
    let receipt ← confirmedReceipt effects signed.transactionHash (400 + i * 100)
    if receipt.origin != sender || receipt.to != some step.to then
      throw <| IO.userError s!"Receipt sender or target differs; reconcile {fixedHex signed.transactionHash}."
    if !receipt.success then
      statuses := statuses.set! i .reverted
      let reverted ← fromExcept <| journalBytes invoice sender steps statuses hashes
      effects.replaceJournal journal reverted
      throw <| IO.userError s!"Transaction {fixedHex signed.transactionHash} reverted."
    if step.kind == .deposit then
      let expected : Events.ExpectedDeposit := ⟨step.pool, step.commitment⟩
      if RpcReceipt.depositOutcome receipt signed.transactionHash expected != .confirmed then
        throw <| IO.userError s!"Receipt lacks the exact Deposit event; reconcile {fixedHex signed.transactionHash}."
    else
      let allowance ← rpcWordWith effects (500 + i * 20) step.to
        (Abi.selector "allowance(address,address)" ++
          (← fromExcept <| Abi.addressWord sender) ++
          (← fromExcept <| Abi.addressWord step.spender))
      if allowance != step.approvalAmount then
        throw <| IO.userError s!"Approval did not set the reviewed allowance; reconcile {fixedHex signed.transactionHash}."
    effects.waitFinality receipt
    statuses := statuses.set! i .confirmed
    let confirmed ← fromExcept <| journalBytes invoice sender steps statuses hashes
    effects.replaceJournal journal confirmed
    journal := confirmed
  return s!"Confirmed {steps.size} sequential transaction(s)."

/-- Recheck one observed inclusion before advancing. This is RPC evidence,
    not consensus finality or a guarantee against later chain reorganization. -/
private def waitReceiptDepth (rpc : String) (original : RpcReceipt.Receipt) : IO Unit :=
  ProtectedTxSender.confirmReceiptInclusion rpc original

/-- Explicitly experimental live send. The caller must request this route,
    review each exact transaction, and supply a new private journal path. -/
def experimentalPayInvoice (invoiceFile keyFile rpc journalPath : String)
    (chain : ChainId) (yes : Bool) (nonInteractive : Bool := false) : IO String := do
  let keyPath ← absolutePrivatePath keyFile
  let sender ← NativeSigner.addressFromProtectedFile keyPath
  let invoice ← readInvoice invoiceFile chain
  let (readings, steps) ← readInvoicePlan rpc invoice sender
  let senderText ← fromExcept <| addressText sender
  let keyDirectory := String.intercalate "/" (keyPath.splitOn "/").dropLast
  if keyDirectory.isEmpty then
    throw <| IO.userError "Private key path has no safe parent directory."
  let journalPath ← absolutePrivatePath journalPath
  let claimIdentity := s!"tornado-lean-cli/invoice/v1/{chainNumber chain}/{invoice.pool.address.toLower}/{invoice.commitment.toLower}"
  let claimPath := keyDirectory ++ "/.tornado-invoice-" ++
    bytesToHex (keccak256 claimIdentity.toUTF8) ++ ".claim"
  let senderLock := keyDirectory ++ "/.tornado-sender-" ++
    toString (chainNumber chain) ++ "-" ++ senderText.toLower ++ ".lock"
  let claimBytes := ((Json.mkObj [
    ("version", toJson (1 : Nat)), ("kind", toJson ("invoice-claim" : String)),
    ("chainId", toJson (chainNumber chain)),
    ("pool", toJson invoice.pool.address),
    ("commitment", toJson invoice.commitment),
    ("sender", toJson senderText), ("journal", toJson journalPath)]).compress ++ "\n").toUTF8
  let lockBytes := ((Json.mkObj [
    ("version", toJson (1 : Nat)), ("kind", toJson ("sender-lock" : String)),
    ("sender", toJson senderText), ("journal", toJson journalPath),
    ("claim", toJson claimPath)]).compress ++ "\n").toUTF8
  createProtectedFile .senderLock senderLock lockBytes
  try
    createProtectedFile .invoiceClaim claimPath claimBytes
  catch error =>
    try ProtectedIO.removePrivateExact senderLock lockBytes
    catch _ => pure ()
    throw error
  IO.println s!"Sender: {senderText}; invoice: {invoice.raw}"
  for i in [0:steps.size] do IO.println (← renderStep i steps[i]!)
  IO.println s!"Journal: {journalPath}"
  IO.println s!"Permanent invoice claim: {claimPath}"
  IO.println s!"Sender lock until exact confirmation: {senderLock}"
  let effects : Effects := {
    rpc := HttpTransport.call rpc,
    createJournal := createProtectedFile .journal journalPath,
    replaceJournal := WithdrawalJournalProgram.replaceProtected journalPath,
    sign := NativeSigner.sign1559FromProtectedFile keyPath,
    waitFinality := waitReceiptDepth rpc,
    approve := fun review => do
      IO.println review
      if !yes && !nonInteractive then
        IO.println "Type SEND to sign and submit this one transaction:"
        let answer ← (← IO.getStdin).getLine
        if jsTrim answer != "SEND" then
          throw <| IO.userError "Deposit submission cancelled before signing." }
  let result ← try executeWith effects invoice sender readings
    catch error =>
      throw <| IO.userError s!"{error}; sender lock remains at {senderLock}. Inspect the journal and chain before clearing it or retrying."
  ProtectedIO.removePrivateExact senderLock lockBytes
  return result

end Tornado.Cli.DepositSend

#print axioms Tornado.Cli.DepositSend.planInvoice_success_decodes
#print axioms Tornado.Cli.DepositSend.certifySignedStep_success_decodes
