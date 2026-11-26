import Tornado.Cli.DepositSend
import Tornado.Runtime.NativeSigner
import Tornado.Domain.Simple7702
import Tornado.Runtime.Bundler

/-!
Read-only multi-note deposit planning for the pinned CLI's sequential and
Simple7702 routes. Private note backups are reduced to public commitments in
memory; no note secret is printed, journaled, signed, or sent. This module has
no broadcast path. Live chain claims are checked against the pinned catalog,
but RPC honesty and chain finality remain external assumptions.
-/

namespace Tornado.Cli.DepositMulti

open Lean Tornado.Domain Tornado.Protocol Tornado.Crypto Tornado.Runtime

structure Item where
  pool : Pool
  commitment : ByteArray
  deriving Inhabited, BEq

structure PoolReading where
  address : Nat
  denomination : Nat
  allowance : Nat := 0
  deriving Inhabited

structure Readings where
  chainId : Nat
  senderCode : ByteArray
  ethBalance : Nat
  tokenBalance : Nat := 0
  pools : Array PoolReading
  deriving Inhabited

inductive Mode where
  | sequential | simple7702
  deriving Repr, BEq, Inhabited

inductive Reason where
  | forcedSequential | contractOrDelegated | singleDeposit | undelegatedEOA
  | forcedDelegated | compatibleDelegation
  deriving Repr, BEq, Inhabited

structure Plan where
  mode : Mode
  reason : Reason
  noteCount : Nat
  amount : Nat
  batches : Array (Array DepositSend.Step)
  deriving Inhabited

private def fromExcept (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def addressNat (raw : String) : Except String Nat := do
  if !raw.startsWith "0x" then throw "Invalid catalog pool or token address."
  let bytes ← parseHexBytes raw
  if bytes.size != 20 then throw "Invalid catalog pool or token address."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def addressText (value : Nat) : Except String String := do
  if value == 0 || value >= 2 ^ 160 then throw "Invalid sender or pool address."
  let word ← Abi.addressWord value
  return "0x" ++ bytesToHex (word.extract 12 32)

private def hex (bytes : ByteArray) : String := "0x" ++ bytesToHex bytes

/-- The TypeScript batch splitter avoids a singleton trailing batch. -/
def splitItems (items : Array Item) (limit : Nat) : Except String (Array (Array Item)) := do
  if items.isEmpty || limit < 2 || limit > 12 || items.size > 100 then
    throw "Invalid multi-note deposit batch size."
  let mut chunks := #[]
  let mut index := 0
  while index < items.size do
    let remaining := items.size - index
    let take := if remaining > limit && remaining - limit == 1
      then limit - 1 else min limit remaining
    if take == 0 then throw "Invalid deposit batch split."
    chunks := chunks.push (items.extract index (index + take))
    index := index + take
  return chunks

def validateItems (items : Array Item) (chain : ChainId) :
    Except String Unit := do
  if items.isEmpty || items.size > 100 then
    throw "Use 1–100 supported notes in one deposit session."
  let first := items[0]!
  let mut commitments : Array ByteArray := #[]
  for item in items do
    if item.pool.chainId != chain ||
        item.pool.asset.symbol != first.pool.asset.symbol ||
        item.pool.asset.token != first.pool.asset.token ||
        !(allPools.any (fun known => known == item.pool)) ||
        item.commitment.size != 32 || commitments.contains item.commitment then
      throw "Deposit notes have a wrong network, asset, pool, commitment, or duplicate."
    commitments := commitments.push item.commitment

private def uniquePools (items : Array Item) : Array Pool := Id.run do
  let mut pools := #[]
  let mut seen : Array String := #[]
  for item in items do
    let key := item.pool.address.toLower
    if !seen.contains key then
      seen := seen.push key
      pools := pools.push item.pool
  return pools

private def poolReading (readings : Readings) (pool : Pool) : Except String PoolReading := do
  let address ← addressNat pool.address
  let found := readings.pools.filter (fun row => row.address == address)
  if found.size != 1 then throw "Selected pool has no unique on-chain reading."
  let row := found[0]!
  if row.denomination != pool.amount then
    throw "On-chain pool denomination differs from the pinned catalog."
  return row

def depositStep (item : Item) : Except String DepositSend.Step := do
  let to ← addressNat item.pool.address
  let data ← Abi.poolDeposit item.commitment
  return ⟨.deposit,
    s!"Deposit {item.pool.denomination} {item.pool.asset.symbol}",
    to, data, if item.pool.asset.token.isSome then 0 else item.pool.amount,
    to, item.commitment, 0, 0⟩

private def stepsFor (items : Array Item) (readings : Readings) :
    Except String (Array DepositSend.Step) := do
  let mut steps := #[]
  for pool in uniquePools items do
    let row ← poolReading readings pool
    if let some tokenText := pool.asset.token then
      let token ← addressNat tokenText
      let needed := (items.filter (fun item => item.pool.address.toLower ==
        pool.address.toLower)).foldl (fun sum item => sum + item.pool.amount) 0
      if row.allowance < needed then
        if row.allowance > 0 then
          steps := steps.push ⟨.reset,
            s!"Reset {pool.asset.symbol} approval for {pool.denomination} pool",
            token, (← Abi.erc20Approve row.address 0), 0, 0,
            ByteArray.empty, row.address, 0⟩
        steps := steps.push ⟨.approve,
          s!"Approve exactly {needed} base units of {pool.asset.symbol}",
          token, (← Abi.erc20Approve row.address needed), 0, 0,
          ByteArray.empty, row.address, needed⟩
  for item in items do steps := steps.push (← depositStep item)
  return steps

/-- Pure route planner over validated public commitments and a single RPC
    reading snapshot. Later batch approvals are intentionally left to fresh
    re-planning; this pure function does not sign subsequent batches. -/
private def planCandidate (items : Array Item) (chain : ChainId) (sender : Nat)
    (readings : Readings) (forceSequential : Bool := false)
    (forceDelegated : Bool := false) (entryPointGasCredit : Nat := 0) : Except String Plan := do
  if forceSequential && forceDelegated then
    throw "Sequential and delegated deposit routes cannot both be forced."
  if forceDelegated && !Simple7702.mayForceDelegated readings.senderCode then
    throw "Forced delegation requires an EOA or an EIP-7702 delegation designator."
  validateItems items chain
  if sender == 0 || sender >= 2 ^ 160 ||
      readings.chainId != chainNumber chain then
    throw "Sender or RPC network differs from selected deposit network."
  let total := items.foldl (fun sum item => sum + item.pool.amount) 0
  for pool in uniquePools items do
    let _ ← poolReading readings pool
  if entryPointGasCredit >= Abi.maxUint256 then
    throw "EntryPoint gas credit is outside uint256."
  let usesGasCredit := !forceSequential &&
    (forceDelegated || (items.size > 1 &&
      (readings.senderCode.isEmpty || Simple7702.isCompatible readings.senderCode))) &&
    entryPointGasCredit > 0
  if items[0]!.pool.asset.token.isSome then
    if readings.tokenBalance < total || (readings.ethBalance == 0 && !usesGasCredit) then
      throw "Sender lacks the selected tokens or ETH gas balance."
  else if readings.ethBalance < total || (readings.ethBalance == total && !usesGasCredit) then
    throw "Sender needs the selected ETH plus gas."
  if forceSequential then
    return ⟨.sequential, .forcedSequential, items.size, total,
      #[(← stepsFor items readings)]⟩
  if !forceDelegated && items.size == 1 then
    return ⟨.sequential, .singleDeposit, 1, total,
      #[(← stepsFor items readings)]⟩
  let compatible := Simple7702.isCompatible readings.senderCode
  if !forceDelegated && !compatible && !readings.senderCode.isEmpty then
    return ⟨.sequential, .contractOrDelegated, items.size, total,
      #[(← stepsFor items readings)]⟩
  let chunks ← splitItems items (depositBatchLimit items[0]!.pool.asset)
  let first ← stepsFor chunks[0]! readings
  let mut batches := #[first]
  for i in [1:chunks.size] do
    let mut calls := #[]
    for item in chunks[i]! do calls := calls.push (← depositStep item)
    batches := batches.push calls
  let reason := if forceDelegated then Reason.forcedDelegated
    else if compatible then .compatibleDelegation else .undelegatedEOA
  return ⟨.simple7702, reason, items.size, total, batches⟩

/-- Public semantic input retains the exact selected commitment order and
catalog amounts, separately from the candidate calldata. -/
def planIntent (items : Array Item) (chain : ChainId) (sender : Nat)
    (readings : Readings) (forceSequential : Bool) (forceDelegated : Bool := false)
    (entryPointGasCredit : Nat := 0) :
    Except String DepositIntent.Input := do
  let selected ← items.mapM fun item => do
    let pool ← addressNat item.pool.address
    let token : Option Nat ← match item.pool.asset.token with
      | none => pure none
      | some text => some <$> addressNat text
    return ({
      pool, denomination := item.pool.amount, token,
      commitment := item.commitment.data } : DepositIntent.Item)
  return {
    items := selected, sender, chainId := chainNumber chain, actualChainId := readings.chainId,
    senderCode := readings.senderCode.data, ethBalance := readings.ethBalance,
    tokenBalance := readings.tokenBalance,
    pools := readings.pools.map (fun row => ⟨row.address, row.denomination, row.allowance⟩),
    forceSequential, forceDelegated, limit := depositBatchLimit items[0]!.pool.asset,
    entryPointGasCredit }

def planEncoding (plan : Plan) : DepositIntent.EncodedPlan := {
  mode := match plan.mode with | .sequential => .sequential | .simple7702 => .simple7702
  reason := match plan.reason with
    | .forcedSequential => .forcedSequential | .contractOrDelegated => .contractOrDelegated
    | .singleDeposit => .singleDeposit | .undelegatedEOA => .undelegatedEOA
    | .forcedDelegated => .forcedDelegated | .compatibleDelegation => .compatibleDelegation
  noteCount := plan.noteCount, amount := plan.amount,
  batches := plan.batches.map (fun steps => steps.map DepositSend.stepEncoding) }

structure PreparedPlan (items : Array Item) (chain : ChainId) (sender : Nat)
    (readings : Readings) (forceSequential : Bool) (forceDelegated : Bool := false)
    (entryPointGasCredit : Nat := 0) where
  private mk ::
  output : Plan
  input : DepositIntent.Input
  original : planIntent items chain sender readings forceSequential forceDelegated entryPointGasCredit = .ok input
  checked : DepositIntent.Checked input (planEncoding output)

def preparePlan (items : Array Item) (chain : ChainId) (sender : Nat)
    (readings : Readings) (forceSequential : Bool := false) (forceDelegated : Bool := false)
    (entryPointGasCredit : Nat := 0) :
    Except String (PreparedPlan items chain sender readings forceSequential forceDelegated entryPointGasCredit) :=
  match planCandidate items chain sender readings forceSequential forceDelegated entryPointGasCredit with
  | .error error => .error error
  | .ok output =>
    match original : planIntent items chain sender readings forceSequential forceDelegated entryPointGasCredit with
    | .error error => .error error
    | .ok input =>
      match DepositIntent.accept input (planEncoding output) with
      | .error error => .error error
      | .ok checked => .ok ⟨output, input, original, checked⟩

/-- Certificates bind every actual planner result to original public items
and this exact snapshot, including fresh forced replanning of later chunks. -/
def plan (items : Array Item) (chain : ChainId) (sender : Nat)
    (readings : Readings) (forceSequential : Bool := false) (forceDelegated : Bool := false)
    (entryPointGasCredit : Nat := 0) : Except String Plan :=
  (preparePlan items chain sender readings forceSequential forceDelegated entryPointGasCredit).map (·.output)

theorem plan_success_decodes (items : Array Item) (chain : ChainId) (sender : Nat)
    (readings : Readings) (forceSequential : Bool) (output : Plan)
    {forceDelegated : Bool} {entryPointGasCredit : Nat}
    (built : plan items chain sender readings forceSequential forceDelegated entryPointGasCredit = .ok output) :
    ∃ input meaning, planIntent items chain sender readings forceSequential forceDelegated entryPointGasCredit = .ok input ∧
      DepositIntent.expected input = .ok meaning ∧
      DepositIntent.decodePlan (planEncoding output) = .ok meaning ∧
      DepositIntent.PlanPolicy input meaning := by
  cases prepared : preparePlan items chain sender readings forceSequential forceDelegated entryPointGasCredit with
  | error error => simp [plan, prepared, Except.map] at built
  | ok result =>
    have same : result.output = output := by simpa [plan, prepared, Except.map] using built
    subst output
    exact ⟨result.input, result.checked.meaning, result.original,
      result.checked.original, result.checked.decoded, result.checked.policy⟩

theorem plan_success_routing (items : Array Item) (chain : ChainId) (sender : Nat)
    (readings : Readings) (forceSequential : Bool) (output : Plan)
    {forceDelegated : Bool} {entryPointGasCredit : Nat}
    (built : plan items chain sender readings forceSequential forceDelegated entryPointGasCredit = .ok output) :
    ∃ input meaning, planIntent items chain sender readings forceSequential forceDelegated entryPointGasCredit = .ok input ∧
      DepositIntent.expected input = .ok meaning ∧
      DepositIntent.decodePlan (planEncoding output) = .ok meaning ∧
      DepositIntent.RoutingPolicy input meaning := by
  obtain ⟨input, meaning, original, expected, decoded, policy⟩ :=
    plan_success_decodes items chain sender readings forceSequential output
      (forceDelegated := forceDelegated) (entryPointGasCredit := entryPointGasCredit) built
  exact ⟨input, meaning, original, expected, decoded, policy.2.2.2.2.2.1⟩

/-- Parse a protected backup to public commitments. The returned list has no
    preimages; callers must not retain or print the original backup text. -/
def publicItems (raw : String) (chain : ChainId) : Except String (Array Item) := do
  let candidates ← parseBackupNotes raw chain
  if candidates.length > 100 then throw "Use at most 100 notes in one deposit session."
  let backup ← parseDepositBackup raw chain
  let mut items := #[]
  for entry in backup do
    let commitment ← parseHexBytes entry.publicIdentity.commitment
    if commitment.size != 32 then throw "Generated note commitment is not bytes32."
    items := items.push ⟨entry.note.pool, commitment⟩
  return items

private def rpcQuantity (value : Json) : IO Nat := do
  let raw ← fromExcept value.getStr?
  fromExcept <| JsonRpc.parseHexQuantity raw

private def rpcWord (value : Json) : IO Nat := do
  let raw ← fromExcept value.getStr?
  let bytes ← fromExcept <| parseHexBytes raw
  if !raw.startsWith "0x" || bytes.size != 32 then
    throw <| IO.userError "RPC contract call did not return uint256."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def callWord (rpc : String) (id target : Nat) (data : ByteArray) : IO Nat := do
  let to ← fromExcept <| addressText target
  let result ← HttpTransport.call rpc id .call
    #[Json.mkObj [("to", toJson to), ("data", toJson (hex data))],
      toJson ("latest" : String)]
  rpcWord result

/-- Read the sender's own gas credit only for an eligible Simple7702 route.
This remains a separate real input: EntryPoint credit cannot fund deposit
principal or gas for an ordinary sequential transaction. -/
def gasCreditForPlan (rpc : String) (items : Array Item) (sender : Nat)
    (readings : Readings) (forceSequential : Bool := false)
    (forceDelegated : Bool := false) : IO Nat := do
  if forceSequential || (!forceDelegated && (items.size == 1 ||
      (!readings.senderCode.isEmpty && !Simple7702.isCompatible readings.senderCode))) then
    return 0
  try
    callWord rpc 1000 Bundler.entryPoint (Abi.selector "balanceOf(address)" ++
      (← fromExcept <| Abi.addressWord sender))
  catch _ =>
    throw <| IO.userError "Could not read the sender's EntryPoint gas credit. Check the RPC endpoint."

/-- Read route eligibility, aggregate balances and exact denominational and
    allowance values from one selected RPC. This never requests a signature. -/
def liveReadings (rpc : String) (items : Array Item) (chain : ChainId)
    (sender : Nat) : IO Readings := do
  if items.isEmpty then
    throw <| IO.userError "Select at least one supported note."
  let senderText ← fromExcept <| addressText sender
  let chainId ← rpcQuantity (← HttpTransport.call rpc 1 .chainId #[])
  if chainId != chainNumber chain then
    throw <| IO.userError "RPC endpoint is on a different network."
  let codeRaw ← fromExcept <| (← HttpTransport.call rpc 2 .getCode
    #[toJson senderText, toJson ("latest" : String)]).getStr?
  if !codeRaw.startsWith "0x" then
    throw <| IO.userError "RPC sender code is malformed."
  let senderCode ← fromExcept <| parseHexBytes codeRaw
  let ethBalance ← rpcQuantity (← HttpTransport.call rpc 3 .getBalance
    #[toJson senderText, toJson ("pending" : String)])
  let mut tokenBalance := 0
  let mut nextId := 4
  if let some tokenText := items[0]!.pool.asset.token then
    let token ← fromExcept <| addressNat tokenText
    tokenBalance ← callWord rpc nextId token
      (Abi.selector "balanceOf(address)" ++
        (← fromExcept <| Abi.addressWord sender))
    nextId := nextId + 1
  let mut pools := #[]
  for pool in uniquePools items do
    let address ← fromExcept <| addressNat pool.address
    let denomination ← callWord rpc nextId address (Abi.selector "denomination()")
    nextId := nextId + 1
    let mut allowance := 0
    if let some tokenText := pool.asset.token then
      let token ← fromExcept <| addressNat tokenText
      allowance ← callWord rpc nextId token
        (Abi.selector "allowance(address,address)" ++
          (← fromExcept <| Abi.addressWord sender) ++
          (← fromExcept <| Abi.addressWord address))
      nextId := nextId + 1
    pools := pools.push ⟨address, denomination, allowance⟩
  return ⟨chainId, senderCode, ethBalance, tokenBalance, pools⟩

private def absolutePrivatePath (path : String) : IO String := do
  let current ← IO.currentDir
  return if (System.FilePath.mk path).isAbsolute then path
    else (current / path).toString

private def stepText (step : DepositSend.Step) : Except String String := do
  return s!"{step.label}; to {← addressText step.to}; value {step.value} wei; data {hex step.data}"

/-- Runnable dry-run for a protected note backup. Only public commitments and
    exact call data appear in the output. It does not sign, journal, or send. -/
def dryRun (notesFile keyFile rpc : String) (chain : ChainId)
    (forceSequential : Bool := false) (forceDelegated : Bool := false) : IO String := do
  let sender ← NativeSigner.addressFromProtectedFile (← absolutePrivatePath keyFile)
  let bytes ← ProtectedIO.readPrivate (← absolutePrivatePath notesFile)
  let some raw := String.fromUTF8? bytes
    | throw <| IO.userError "Private note backup is not UTF-8."
  let items ← fromExcept <| publicItems raw chain
  let readings ← liveReadings rpc items chain sender
  let gasCredit ← gasCreditForPlan rpc items sender readings forceSequential forceDelegated
  let preview ← fromExcept <| plan items chain sender readings forceSequential forceDelegated gasCredit
  let mut lines := [s!"Sender: {← fromExcept <| addressText sender}",
    s!"Total: {preview.amount} base units of {items[0]!.pool.asset.symbol} across {preview.noteCount} deposit(s)."]
  if preview.mode == .simple7702 then
    lines := lines ++ [s!"Route: {preview.batches.size} Simple7702 UserOperation batch(es)."]
    if Simple7702.isCompatible readings.senderCode then
      lines := lines ++ ["The existing Simple7702 delegation would be reused; no new authorization is needed."]
    else if readings.senderCode.isEmpty then
      lines := lines ++ ["The first batch would authorize Simple7702 on this EOA; delegation would persist."]
    else
      lines := lines ++ ["The first batch would replace the existing delegation with Simple7702; delegation would persist."]
  else
    lines := lines ++ ["Route: sequential EIP-1559 transactions."]
  for i in [0:preview.batches.size] do
    lines := lines ++ [s!"Batch {i + 1}:" ++
      (if i > 0 && preview.mode == .simple7702 then
        " deposit calls only; token approvals require fresh reads before any send."
       else "")]
    for step in preview.batches[i]! do
      lines := lines ++ ["  " ++ (← fromExcept <| stepText step)]
  lines := lines ++ ["Dry run complete. No transaction was signed or submitted."]
  return String.intercalate "\n" lines

end Tornado.Cli.DepositMulti

#print axioms Tornado.Cli.DepositMulti.plan_success_decodes
#print axioms Tornado.Cli.DepositMulti.plan_success_routing
