import Tornado.Domain.Catalog

/-!
Native Lean port of the captured CLI's exact branch-and-bound denomination
planner. The search limit and tie order are part of the compatibility policy.
Its data source is Tornado.Domain.Catalog, not a runtime SDK call.
-/

namespace Tornado.Domain

structure PlanEntry where
  pool : Pool
  count : Nat
  deriving Repr, BEq, Inhabited

structure DenominationPlan where
  amount : Nat
  entries : List PlanEntry
  noteCount : Nat
  batchCount : Nat
  excludedDenominations : Option (List Nat) := none
  deriving Repr, BEq, Inhabited

private def jsMaxSafe : Nat := 9007199254740991

private def ceilDiv (a b : Nat) : Nat :=
  if b == 0 then 0 else (a + b - 1) / b

def planValue (entries : List PlanEntry) : Nat :=
  entries.foldl (fun sum entry => sum + entry.pool.amount * entry.count) 0

def planNoteCount (entries : List PlanEntry) : Nat :=
  entries.foldl (fun count entry => count + entry.count) 0

def planExpectedBatches (entries : List PlanEntry) : Nat :=
  match entries.head? with
  | none => 0
  | some first => ceilDiv (planNoteCount entries) (depositBatchLimit first.pool.asset)

/-- Runtime validation is independent of the branch-and-bound search path.
It cannot establish optimality, but prevents printing an inconsistent plan. -/
def planValidBool (requested : Nat) (available : List Pool) (plan : DenominationPlan) : Bool :=
  decide (requested > 0) &&
  decide (plan.amount = requested) &&
  !plan.entries.isEmpty &&
  decide (planValue plan.entries = requested) &&
  decide (planNoteCount plan.entries = plan.noteCount) &&
  decide (planExpectedBatches plan.entries = plan.batchCount) &&
  plan.entries.all (fun entry => entry.count > 0 && available.contains entry.pool)

def planValid (requested : Nat) (available : List Pool) (plan : DenominationPlan) : Prop :=
  planValidBool requested available plan = true

def validatePlan (requested : Nat) (available : List Pool)
    (plan : DenominationPlan) : Except String Unit :=
  if planValidBool requested available plan then .ok ()
  else .error "Internal denomination plan failed validation."

theorem validatePlan_sound (requested : Nat) (available : List Pool)
    (plan : DenominationPlan)
    (h : validatePlan requested available plan = .ok ()) :
    planValid requested available plan := by
  unfold planValid
  cases hBool : planValidBool requested available plan with
  | false => simp [validatePlan, hBool] at h
  | true => rfl

theorem validatePlan_value (requested : Nat) (available : List Pool)
    (plan : DenominationPlan)
    (h : validatePlan requested available plan = .ok ()) :
    planValue plan.entries = requested := by
  have hValid := validatePlan_sound requested available plan h
  simp only [planValid, planValidBool, Bool.and_eq_true, decide_eq_true_eq] at hValid
  simp_all

/-- Every printed plan has exactly the note count that the CLI announces. -/
theorem validatePlan_note_count (requested : Nat) (available : List Pool)
    (plan : DenominationPlan)
    (h : validatePlan requested available plan = .ok ()) :
    planNoteCount plan.entries = plan.noteCount := by
  have hValid := validatePlan_sound requested available plan h
  simp only [planValid, planValidBool, Bool.and_eq_true, decide_eq_true_eq] at hValid
  simp_all

/-- Every printed plan has exactly the batch count that the CLI announces. -/
theorem validatePlan_batch_count (requested : Nat) (available : List Pool)
    (plan : DenominationPlan)
    (h : validatePlan requested available plan = .ok ()) :
    planExpectedBatches plan.entries = plan.batchCount := by
  have hValid := validatePlan_sound requested available plan h
  simp only [planValid, planValidBool, Bool.and_eq_true, decide_eq_true_eq] at hValid
  simp_all

/-- The runtime guard rejects empty output plans and zero requests. -/
theorem validatePlan_nonempty_positive (requested : Nat) (available : List Pool)
    (plan : DenominationPlan)
    (h : validatePlan requested available plan = .ok ()) :
    requested > 0 ∧ plan.entries.isEmpty = false := by
  have hValid := validatePlan_sound requested available plan h
  simp only [planValid, planValidBool, Bool.and_eq_true, decide_eq_true_eq] at hValid
  simp_all

/-- All entries must use an allowed pool with a strictly positive count. -/
theorem validatePlan_entries_allowed (requested : Nat) (available : List Pool)
    (plan : DenominationPlan)
    (h : validatePlan requested available plan = .ok ()) :
    plan.entries.all (fun entry => entry.count > 0 && available.contains entry.pool) = true := by
  have hValid := validatePlan_sound requested available plan h
  simp only [planValid, planValidBool, Bool.and_eq_true, decide_eq_true_eq] at hValid
  simp_all

#print axioms Tornado.Domain.validatePlan_sound
#print axioms Tornado.Domain.validatePlan_value
#print axioms Tornado.Domain.validatePlan_note_count
#print axioms Tornado.Domain.validatePlan_batch_count
#print axioms Tornado.Domain.validatePlan_nonempty_positive
#print axioms Tornado.Domain.validatePlan_entries_allowed

private def sameCatalog (pools : List Pool) : Except String Unit := do
  let some first := pools.head? | return ()
  if pools.any (fun pool =>
      pool.chainId != first.chainId || pool.asset.symbol != first.asset.symbol ||
      pool.asset.decimals != first.asset.decimals || pool.asset.token != first.asset.token ||
      pool.amount == 0 ||
      (poolFor pool.chainId pool.denomination pool.asset.symbol).map (·.address) != some pool.address) then
    throw "Plan with supported Tornado pools of one asset and one network."

private def uniqueStable [BEq α] (values : List α) : List α :=
  values.foldl (fun acc value => if acc.contains value then acc else acc ++ [value]) []

def parseExcludedDenominations (values : List String) (pools : List Pool) : Except String (List Nat) := do
  sameCatalog pools
  let some first := pools.head?
    | if values.isEmpty then return [] else throw "No supported denominations are available."
  let mut excluded : List Nat := []
  for value in values do
    let parsed := decimalParts value
    if parsed.isNone || (parsed.getD default).fraction.length > first.asset.decimals then
      throw s!"Invalid excluded denomination {value}: use an exact positive amount in token units."
    let some amount := parseUnitsExact value first.asset.decimals
      | throw s!"Invalid excluded denomination {value}: use an exact positive amount in token units."
    if amount == 0 || !(pools.any (fun pool => pool.amount == amount)) then
      throw s!"Excluded denomination {value} is not supported for this asset and chain."
    if !excluded.contains amount then excluded := excluded ++ [amount]
  return excluded

private def insertPoolDesc (pool : Pool) : List Pool → List Pool
  | [] => [pool]
  | head :: tail =>
      if pool.amount > head.amount then pool :: head :: tail
      else head :: insertPoolDesc pool tail

private def sortPoolDesc (pools : List Pool) : List Pool :=
  pools.foldl (fun acc pool => insertPoolDesc pool acc) []

private def gcdAmounts (pools : List Pool) : Nat :=
  pools.foldl (fun acc pool => Nat.gcd acc pool.amount) 0

private structure SearchState where
  best : Option (List PlanEntry) := none
  bestCount : Nat := jsMaxSafe + 1
  visited : Nat := 0

private def search (pools : List Pool) (remaining used : Nat)
    (entries : List PlanEntry) (state : SearchState) : Except String SearchState := do
  let state := { state with visited := state.visited + 1 }
  if state.visited > 100000 then
    throw "Exact Tornado packing search is too large; narrow the allowed denominations."
  if remaining == 0 then
    return { state with best := some entries, bestCount := used }
  match pools with
  | [] => return state
  | pool :: rest =>
      if remaining % gcdAmounts pools != 0 then return state
      if used + ceilDiv remaining pool.amount >= state.bestCount then return state
      match rest with
      | [] =>
          if remaining % pool.amount != 0 then return state
          let count := remaining / pool.amount
          if used + count >= state.bestCount then return state
          return { state with
            best := some (entries ++ [{ pool, count }]), bestCount := used + count }
      | next :: tail =>
          let mut current := state
          let maximum := remaining / pool.amount
          for offset in [0:maximum + 1] do
            current := { current with visited := current.visited + 1 }
            if current.visited > 100000 then
              throw "Exact Tornado packing search is too large; narrow the allowed denominations."
            let count := maximum - offset
            let restAmount := remaining - count * pool.amount
            if used + count + ceilDiv restAmount next.amount >= current.bestCount then break
            if restAmount % gcdAmounts rest != 0 then continue
            let nextEntries := if count == 0 then entries else entries ++ [{ pool, count }]
            current ← search (next :: tail) restAmount (used + count) nextEntries current
          return current
termination_by pools.length

def bestPacking (amount : Nat) (pools : List Pool) : Except String (Option DenominationPlan) := do
  let sorted := sortPoolDesc (pools.filter (fun pool => pool.amount <= amount))
  let some first := sorted.head? | return none
  if sorted.length > 16 then throw "Too many Tornado denominations to plan safely."
  if amount / first.amount > jsMaxSafe then return none
  let state ← search sorted amount 0 [] {}
  let some entries := state.best | return none
  if state.bestCount > jsMaxSafe then return none
  let count := state.bestCount
  return some { amount, entries, noteCount := count, batchCount := ceilDiv count (depositBatchLimit first.asset) }

def requireDenominationPlan (amount : Nat) (pools : List Pool)
    (singleAtomicBatch : Bool := false) : Except String DenominationPlan := do
  if amount == 0 then throw "Amount must be greater than zero."
  sameCatalog pools
  let plan ← bestPacking amount pools
  match plan with
  | some plan =>
      if !singleAtomicBatch || plan.batchCount <= 1 then return plan
  | none => pure ()
  if singleAtomicBatch then
    throw s!"No exact Tornado packing fits within one {pools.head?.map (fun p => depositBatchLimit p.asset) |>.getD 0}-note atomic batch."
  else throw "No exact Tornado packing is possible with these pool exclusions."

private def insertNatDesc (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail => if value > head then value :: head :: tail else head :: insertNatDesc value tail

private def isThreeStyle (value : Nat) : Bool :=
  String.ofList (((toString value).toList.reverse.dropWhile (· == '0')).reverse) == "3"

def denominationPlanChoices (amount : Nat) (pools : List Pool)
    (singleAtomicBatch : Bool := false) : Except String (List DenominationPlan) := do
  if amount == 0 then throw "Amount must be greater than zero."
  sameCatalog pools
  let denominations := (uniqueStable ((pools.filter (fun p => p.amount <= amount)).map (·.amount)))
    |>.foldl (fun acc value => insertNatDesc value acc) []
  let threes := denominations.filter isThreeStyle
  let pairs := (List.range threes.length).flatMap fun i =>
    (threes.drop (i + 1)).map (fun other => [threes[i]!, other])
  let prefixes := (List.range (threes.length - 2)).map fun i => threes.take (i + 3)
  let nonClassic := denominations.filter fun value =>
    pools.any (fun pool => pool.amount == value && !supportsClassicRelayer pool)
  let exclusions := [[]] ++ threes.map (fun value => [value]) ++ pairs ++ prefixes ++
    [nonClassic] ++ denominations.map (fun value => [value])
  let mut plans : List DenominationPlan := []
  let mut seen : List (List (String × Nat)) := []
  for excluded in exclusions do
    let plan ← bestPacking amount (pools.filter (fun pool => !excluded.contains pool.amount))
    if let some plan := plan then
      if !singleAtomicBatch || plan.batchCount <= 1 then
        let key := plan.entries.map (fun entry => (entry.pool.address, entry.count))
        if !seen.contains key then
          seen := seen ++ [key]
          plans := plans ++ [{ plan with excludedDenominations := some excluded }]
  return plans.take 4

def denominationPlanLabel (plan : DenominationPlan) : Except String String := do
  let some first := plan.entries.head? | throw "Cannot describe an empty denomination plan."
  let denoms := plan.entries.map (fun entry => formatUnitsExact entry.pool.amount entry.pool.asset.decimals)
  let noteWord := if plan.noteCount == 1 then "note" else "notes"
  let txWord := if plan.noteCount == 1 then "tx" else "txs"
  return s!"{plan.noteCount} {noteWord} · {String.intercalate ", " denoms} {first.pool.asset.symbol} · {plan.noteCount} sequential deposit {txWord}"

end Tornado.Domain
