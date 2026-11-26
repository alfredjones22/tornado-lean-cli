import Tornado.Protocol.Abi
import Tornado.Protocol.TypedTransactionDecode
import Tornado.Domain.Simple7702

/-! Public deposit intent. Expected steps are numeric catalog/request fields;
the encoded step projections are independently decoded before comparison.
The snapshot is caller supplied and does not authenticate chain state. -/

namespace Tornado.Protocol.DepositIntent

inductive Kind where
  | reset | approve | deposit
  deriving Inhabited, DecidableEq, BEq

inductive Mode where
  | sequential | simple7702
  deriving Inhabited, DecidableEq, BEq

inductive Reason where
  | forcedSequential | contractOrDelegated | singleDeposit | undelegatedEOA
  | forcedDelegated | compatibleDelegation
  deriving Inhabited, DecidableEq, BEq

structure EncodedStep where
  kind : Kind
  to : Nat
  value : Nat
  data : ByteArray
  pool : Nat
  commitment : ByteArray
  spender : Nat
  approvalAmount : Nat
  deriving Inhabited

structure EncodedPlan where
  mode : Mode
  reason : Reason
  noteCount : Nat
  amount : Nat
  batches : Array (Array EncodedStep)
  deriving Inhabited

structure Item where
  pool : Nat
  denomination : Nat
  token : Option Nat
  commitment : Array UInt8
  deriving Inhabited, DecidableEq

structure PoolReading where
  address : Nat
  denomination : Nat
  allowance : Nat
  deriving Inhabited

structure Input where
  items : Array Item
  sender : Nat
  chainId : Nat
  actualChainId : Nat
  senderCode : Array UInt8 := #[]
  ethBalance : Nat
  tokenBalance : Nat
  pools : Array PoolReading
  forceSequential : Bool
  forceDelegated : Bool := false
  limit : Nat
  entryPointGasCredit : Nat := 0
  deriving Inhabited

structure Meaning where
  kind : Kind
  to : Nat
  value : Nat
  commitment : Array UInt8 := #[]
  spender : Nat := 0
  approvalAmount : Nat := 0
  deriving Inhabited, DecidableEq

structure PlanMeaning where
  mode : Mode
  reason : Reason
  noteCount : Nat
  amount : Nat
  batches : Array (Array Meaning)
  deriving Inhabited, DecidableEq

private def word (bytes : ByteArray) (start : Nat) : Except String Nat := do
  if start + 32 > bytes.size then throw "Truncated deposit ABI word."
  return (bytes.extract start (start + 32)).data.foldl (fun n b => n * 256 + b.toNat) 0

/-- Deposit's selector and exact static bytes32 payload are read directly;
no expected commitment or encoder output is supplied to this parser. -/
def decodeDeposit (data : ByteArray) : Except String (Array UInt8) := do
  if data.size != 36 || data.extract 0 4 != Abi.selector "deposit(bytes32)" then
    throw "Noncanonical deposit calldata."
  return (data.extract 4 36).data

/-- ERC-20 approval's exact selector, address word and amount are read from
the actual data. Exact length rejects all extra payload and trailing bytes. -/
def decodeApprove (data : ByteArray) : Except String (Nat × Nat) := do
  if data.size != 68 || data.extract 0 4 != Abi.selector "approve(address,uint256)" then
    throw "Noncanonical approval calldata."
  let spender ← word data 4
  if spender >= Abi.maxAddress then throw "Approval spender is out of range."
  return (spender, ← word data 36)

/-- Journal metadata must agree with the independent calldata fields. -/
def decodeStep (step : EncodedStep) : Except String Meaning := do
  if step.to == 0 || step.to >= Abi.maxAddress || step.value >= Abi.maxUint256 then
    throw "Deposit step target or value is out of range."
  match step.kind with
  | .deposit =>
    let commitment ← decodeDeposit step.data
    if step.pool != step.to || step.commitment.data != commitment ||
        step.spender != 0 || step.approvalAmount != 0 then
      throw "Deposit metadata differs from the decoded call."
    return { kind := .deposit, to := step.to, value := step.value, commitment }
  | kind =>
    let (spender, amount) ← decodeApprove step.data
    if step.value != 0 || step.pool != 0 || !step.commitment.isEmpty ||
        step.spender != spender || step.approvalAmount != amount ||
        (kind == .reset && amount != 0) then
      throw "Approval metadata differs from the decoded call."
    return { kind, to := step.to, value := 0, spender, approvalAmount := amount }

def decodeSteps (steps : Array EncodedStep) : Except String (Array Meaning) :=
  steps.mapM decodeStep

def decodePlan (plan : EncodedPlan) : Except String PlanMeaning := do
  let batches ← plan.batches.mapM decodeSteps
  return {
    mode := plan.mode, reason := plan.reason, noteCount := plan.noteCount,
    amount := plan.amount, batches }

def deposit (item : Item) : Meaning := {
  kind := .deposit, to := item.pool,
  value := if item.token.isSome then 0 else item.denomination,
  commitment := item.commitment }

private def uniquePools (items : Array Item) : Array Item :=
  items.foldl (fun seen item =>
    if seen.any (fun old => old.pool == item.pool) then seen else seen.push item) #[]

def total (items : Array Item) : Nat :=
  items.foldl (fun sum item => sum + item.denomination) 0

private def reading (input : Input) (item : Item) : Except String PoolReading := do
  let found := input.pools.filter (fun row => row.address == item.pool)
  if found.size != 1 || found[0]!.denomination != item.denomination then
    throw "Deposit intent has no unique matching denomination reading."
  return found[0]!

/-- Approvals are bounded to exactly the selected per-pool sum. A nonzero
insufficient allowance is reset, then replaced; sufficient allowance adds no
approval. No calldata encoder participates in this semantic construction. -/
def approvals (input : Input) (items : Array Item) : Except String (Array Meaning) := do
  let mut result := #[]
  for item in uniquePools items do
    let row ← reading input item
    if let some token := item.token then
      let needed := total (items.filter (fun selected => selected.pool == item.pool))
      if row.allowance < needed then
        if row.allowance > 0 then
          result := result.push {
            kind := .reset, to := token, value := 0,
            spender := item.pool, approvalAmount := 0 }
        result := result.push {
          kind := .approve, to := token, value := 0,
          spender := item.pool, approvalAmount := needed }
  return result

def sequentialSteps (input : Input) (items : Array Item) : Except String (Array Meaning) := do
  return (← approvals input items) ++ items.map deposit

/-- A bounded structural specification of the existing splitter. The final
pair is kept together when taking a full chunk would leave one item. -/
def chunks : Nat → Array Item → Nat → Except String (Array (Array Item))
  | 0, items, _ => if items.isEmpty then .ok #[] else .error "Deposit split fuel exhausted."
  | fuel + 1, items, limit => do
    if items.isEmpty then return #[]
    let take := if items.size > limit && items.size - limit == 1 then limit - 1
      else min limit items.size
    if take == 0 then throw "Invalid semantic deposit chunk."
    let remaining ← chunks fuel (items.extract take items.size) limit
    return #[items.extract 0 take] ++ remaining

/-- Independent semantic plan derived solely from original public items and
the indexed reading snapshot. Later 7702 chunks deliberately contain deposits
only; their actual approvals are determined by fresh forced replanning. -/
def expected (input : Input) : Except String PlanMeaning := do
  if input.forceSequential && input.forceDelegated then
    throw "Sequential and delegated deposit routes cannot both be forced."
  let code := ByteArray.mk input.senderCode
  if input.forceDelegated && !Tornado.Domain.Simple7702.mayForceDelegated code then
    throw "Forced delegation requires an EOA or an EIP-7702 delegation designator."
  if input.items.isEmpty || input.items.size > 100 || input.limit < 2 || input.limit > 12 ||
      input.sender == 0 || input.sender >= Abi.maxAddress || input.chainId != input.actualChainId then
    throw "Invalid deposit semantic scope."
  let first := input.items[0]!
  if input.limit != (if first.token.isSome then 5 else 12) then
    throw "Deposit intent chunk limit differs from the selected asset policy."
  let mut commitments : Array (Array UInt8) := #[]
  for item in input.items do
    if item.pool == 0 || item.pool >= Abi.maxAddress || item.denomination == 0 ||
        item.token != first.token || item.commitment.size != 32 || commitments.contains item.commitment then
      throw "Invalid ordered deposit intent item."
    if let some token := item.token then
      if token == 0 || token >= Abi.maxAddress then throw "Invalid deposit token address."
    let _ ← reading input item
    commitments := commitments.push item.commitment
  let amount := total input.items
  if input.entryPointGasCredit >= Abi.maxUint256 then
    throw "EntryPoint gas credit is outside uint256."
  let usesGasCredit := !input.forceSequential &&
    (input.forceDelegated || (input.items.size > 1 &&
      (code.isEmpty || Tornado.Domain.Simple7702.isCompatible code))) &&
    input.entryPointGasCredit > 0
  if first.token.isSome then
    if input.tokenBalance < amount || (input.ethBalance == 0 && !usesGasCredit) then
      throw "Insufficient deposit intent balance."
  else if input.ethBalance < amount || (input.ethBalance == amount && !usesGasCredit) then
    throw "Insufficient deposit ETH intent balance."
  if input.forceSequential then
    return {
      mode := .sequential, reason := .forcedSequential,
      noteCount := input.items.size, amount, batches := #[← sequentialSteps input input.items] }
  if !input.forceDelegated && input.items.size == 1 then
    return {
      mode := .sequential, reason := .singleDeposit,
      noteCount := 1, amount, batches := #[← sequentialSteps input input.items] }
  let compatible := Tornado.Domain.Simple7702.isCompatible code
  if !input.forceDelegated && !compatible && !code.isEmpty then
    return {
      mode := .sequential, reason := .contractOrDelegated,
      noteCount := input.items.size, amount, batches := #[← sequentialSteps input input.items] }
  let selected ← chunks 100 input.items input.limit
  let firstSteps ← sequentialSteps input selected[0]!
  let later := (selected.extract 1 selected.size).map (fun chunk => chunk.map deposit)
  return {
    mode := .simple7702,
    reason := if input.forceDelegated then .forcedDelegated
      else if compatible then .compatibleDelegation else .undelegatedEOA,
    noteCount := input.items.size, amount, batches := #[firstSteps] ++ later }

/-- The routing decision is bound to the original complete code bytes, note
count and both force flags. One note defaults to ordinary transactions;
forced delegation admits only empty code or a valid designator. -/
def RoutingPolicy (input : Input) (meaning : PlanMeaning) : Prop :=
  ¬ (input.forceSequential = true ∧ input.forceDelegated = true) ∧
  (if input.forceSequential then
    meaning.mode = .sequential ∧ meaning.reason = .forcedSequential
  else if input.forceDelegated then
    Tornado.Domain.Simple7702.mayForceDelegated (ByteArray.mk input.senderCode) = true ∧
    meaning.mode = .simple7702 ∧ meaning.reason = .forcedDelegated
  else if input.items.size = 1 then
    meaning.mode = .sequential ∧ meaning.reason = .singleDeposit
  else if Tornado.Domain.Simple7702.isCompatible (ByteArray.mk input.senderCode) then
    meaning.mode = .simple7702 ∧ meaning.reason = .compatibleDelegation
  else if input.senderCode.isEmpty then
    meaning.mode = .simple7702 ∧ meaning.reason = .undelegatedEOA
  else meaning.mode = .sequential ∧ meaning.reason = .contractOrDelegated)

instance (input : Input) (meaning : PlanMeaning) : Decidable (RoutingPolicy input meaning) := by
  unfold RoutingPolicy
  infer_instance

/-- Explicit conservation requirements over decoded calls. Every selected
commitment is funded exactly once and in order, with the catalog pool and
ETH value. The count/sum and route bounds refer to original public items. -/
def PlanPolicy (input : Input) (meaning : PlanMeaning) : Prop :=
  meaning.noteCount = input.items.size ∧ meaning.amount = total input.items ∧
  ((meaning.batches.toList.flatMap (·.toList)).filter (fun step => step.kind == .deposit)) =
    (input.items.map deposit).toList ∧
  0 < meaning.batches.size ∧ meaning.batches.size ≤ 100 ∧
  RoutingPolicy input meaning ∧
  (if meaning.mode = .sequential then meaning.batches.size = 1 else
    meaning.batches.all (fun steps =>
      let count := (steps.filter (fun step => step.kind == .deposit)).size
      decide (0 < count ∧ count ≤ input.limit ∧ steps.size ≤ 15)) = true)

instance (input : Input) (meaning : PlanMeaning) : Decidable (PlanPolicy input meaning) := by
  unfold PlanPolicy
  infer_instance

structure Checked (input : Input) (plan : EncodedPlan) where
  private mk ::
  meaning : PlanMeaning
  original : expected input = .ok meaning
  decoded : decodePlan plan = .ok meaning
  policy : PlanPolicy input meaning

def accept (input : Input) (plan : EncodedPlan) : Except String (Checked input plan) :=
  match original : expected input with
  | .error error => .error error
  | .ok meaning =>
    match decoded : decodePlan plan with
    | .error error => .error error
    | .ok actual =>
      if agreement : actual = meaning then
        if policy : PlanPolicy input meaning then .ok ⟨meaning, original, agreement ▸ decoded, policy⟩
        else .error "Deposit plan violates conservation or chunk bounds."
      else .error "Encoded deposit plan differs from the original public intent."

structure CheckedSteps (input : Input) (steps : Array EncodedStep) where
  private mk ::
  meaning : PlanMeaning
  original : expected input = .ok meaning
  sequential : meaning.mode = .sequential
  singleBatch : meaning.batches.size = 1
  decoded : decodeSteps steps = .ok meaning.batches[0]!
  policy : PlanPolicy input meaning

def acceptSteps (input : Input) (steps : Array EncodedStep) :
    Except String (CheckedSteps input steps) :=
  match original : expected input with
  | .error error => .error error
  | .ok meaning =>
    if sequential : meaning.mode = .sequential then
      if singleBatch : meaning.batches.size = 1 then
        match decoded : decodeSteps steps with
        | .error error => .error error
        | .ok actual =>
          if agreement : actual = meaning.batches[0]! then
            if policy : PlanPolicy input meaning then
              .ok ⟨meaning, original, sequential, singleBatch, agreement ▸ decoded, policy⟩
            else .error "Sequential deposit intent violates conservation."
          else .error "Sequential deposit steps differ from public intent."
      else .error "Sequential deposit intent requires one batch."
    else .error "Sequential deposit intent has a different route."

theorem checked_complete_intent (input : Input) (plan : EncodedPlan) (checked : Checked input plan) :
    ∃ meaning, expected input = .ok meaning ∧ decodePlan plan = .ok meaning ∧
      PlanPolicy input meaning :=
  ⟨checked.meaning, checked.original, checked.decoded, checked.policy⟩

theorem checked_sequential_intent (input : Input) (steps : Array EncodedStep)
    (checked : CheckedSteps input steps) :
    ∃ meaning, expected input = .ok meaning ∧ meaning.mode = .sequential ∧
      meaning.batches.size = 1 ∧ decodeSteps steps = .ok meaning.batches[0]! :=
  ⟨checked.meaning, checked.original, checked.sequential, checked.singleBatch, checked.decoded⟩

theorem checked_ordered_funding (input : Input) (plan : EncodedPlan) (checked : Checked input plan) :
    checked.meaning.noteCount = input.items.size ∧ checked.meaning.amount = total input.items ∧
    (checked.meaning.batches.toList.flatMap (·.toList)).filter (fun step => step.kind == .deposit) =
      (input.items.map deposit).toList :=
  ⟨checked.policy.1, checked.policy.2.1, checked.policy.2.2.1⟩

theorem checked_routing (input : Input) (plan : EncodedPlan) (checked : Checked input plan) :
    RoutingPolicy input checked.meaning := checked.policy.2.2.2.2.2.1

theorem routing_compatible_auto (input : Input) (meaning : PlanMeaning)
    (policy : RoutingPolicy input meaning) (sequential : input.forceSequential = false)
    (forced : input.forceDelegated = false)
    (multiple : input.items.size ≠ 1)
    (compatible : Tornado.Domain.Simple7702.isCompatible (ByteArray.mk input.senderCode) = true) :
    meaning.mode = .simple7702 ∧ meaning.reason = .compatibleDelegation := by
  simpa [RoutingPolicy, sequential, forced, multiple, compatible] using policy

theorem routing_single_default (input : Input) (meaning : PlanMeaning)
    (policy : RoutingPolicy input meaning) (sequential : input.forceSequential = false)
    (forced : input.forceDelegated = false) (single : input.items.size = 1) :
    meaning.mode = .sequential ∧ meaning.reason = .singleDeposit := by
  simpa [RoutingPolicy, sequential, forced, single] using policy

theorem routing_forced_admission (input : Input) (meaning : PlanMeaning)
    (policy : RoutingPolicy input meaning) (sequential : input.forceSequential = false)
    (forced : input.forceDelegated = true) :
    Tornado.Domain.Simple7702.mayForceDelegated (ByteArray.mk input.senderCode) = true ∧
      meaning.mode = .simple7702 ∧ meaning.reason = .forcedDelegated := by
  simpa [RoutingPolicy, sequential, forced] using policy

def TransactionMatches (requested actual : Rlp.Transaction1559) : Prop :=
  actual.chainId = requested.chainId ∧ actual.nonce = requested.nonce ∧
  actual.maxPriorityFeePerGas = requested.maxPriorityFeePerGas ∧
  actual.maxFeePerGas = requested.maxFeePerGas ∧ actual.gas = requested.gas ∧
  actual.to = requested.to ∧ actual.value = requested.value ∧
  actual.data.data = requested.data.data ∧ actual.accessList.isEmpty = true

instance (requested actual : Rlp.Transaction1559) : Decidable (TransactionMatches requested actual) := by
  unfold TransactionMatches
  infer_instance

def StepMatches (step : EncodedStep) (tx : Rlp.Transaction1559) : Prop :=
  tx.to = some step.to ∧ tx.value = step.value ∧ tx.data.data = step.data.data

instance (step : EncodedStep) (tx : Rlp.Transaction1559) : Decidable (StepMatches step tx) := by
  unfold StepMatches
  infer_instance

def executableStep (step : EncodedStep) (tx : Rlp.Transaction1559) : EncodedStep :=
  { step with to := tx.to.getD 0, value := tx.value, data := tx.data }

structure CheckedSignedStep (step : EncodedStep) (requested : Rlp.Transaction1559)
    (raw : ByteArray) where
  private mk ::
  actual : TypedTransactionDecode.Canonical1559 raw
  parsed : TypedTransactionDecode.decode1559 raw = .ok actual
  signed : actual.signature.isSome = true
  preserved : TransactionMatches requested actual.tx
  selected : StepMatches step requested
  meaning : Meaning
  reviewed : decodeStep step = .ok meaning
  executable : decodeStep (executableStep step actual.tx) = .ok meaning

/-- The strict typed-transaction decoder and independent ABI reader bind the
signed executable bytes to the reviewed step. Signature recovery and callback
identity remain the separate protected signer's contract. -/
def acceptSignedStep (step : EncodedStep) (requested : Rlp.Transaction1559) (raw : ByteArray) :
    Except String (CheckedSignedStep step requested raw) :=
  match parsed : TypedTransactionDecode.decode1559 raw with
  | .error error => .error error
  | .ok actual =>
    if signed : actual.signature.isSome = true then
      if preserved : TransactionMatches requested actual.tx then
        if selected : StepMatches step requested then
          match reviewed : decodeStep step with
          | .error error => .error error
          | .ok meaning =>
            match executable : decodeStep (executableStep step actual.tx) with
            | .error error => .error error
            | .ok output =>
              if agreement : output = meaning then
                .ok ⟨actual, parsed, signed, preserved, selected, meaning,
                  reviewed, agreement ▸ executable⟩
              else .error "Signed ABI step differs from reviewed deposit intent."
        else .error "Requested transaction differs from reviewed deposit step."
      else .error "Signed transaction differs from reviewed fields."
    else .error "Deposit transaction has no signature."

theorem checked_signed_step (step : EncodedStep) (requested : Rlp.Transaction1559)
    (raw : ByteArray) (checked : CheckedSignedStep step requested raw) :
    ∃ actual : TypedTransactionDecode.Canonical1559 raw,
      TypedTransactionDecode.decode1559 raw = .ok actual ∧ actual.signature.isSome = true ∧
      TransactionMatches requested actual.tx ∧ StepMatches step requested ∧
      ∃ meaning, decodeStep step = .ok meaning ∧
        decodeStep (executableStep step actual.tx) = .ok meaning :=
  ⟨checked.actual, checked.parsed, checked.signed, checked.preserved, checked.selected,
    checked.meaning, checked.reviewed, checked.executable⟩

end Tornado.Protocol.DepositIntent

#print axioms Tornado.Protocol.DepositIntent.checked_complete_intent
#print axioms Tornado.Protocol.DepositIntent.checked_sequential_intent
#print axioms Tornado.Protocol.DepositIntent.checked_ordered_funding
#print axioms Tornado.Protocol.DepositIntent.checked_routing
#print axioms Tornado.Protocol.DepositIntent.routing_compatible_auto
#print axioms Tornado.Protocol.DepositIntent.routing_single_default
#print axioms Tornado.Protocol.DepositIntent.routing_forced_admission
#print axioms Tornado.Protocol.DepositIntent.checked_signed_step
