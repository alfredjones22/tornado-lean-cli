import Tornado.Domain.Plan
open Tornado.Domain

def checkLine (line : String) : Except String (Nat × Nat × Bool) := do
  let [maskText, valueText, status, entryText] := line.splitOn ","
    | throw s!"Malformed fixture: {line}"
  let some mask := maskText.toNat? | throw s!"Bad mask {maskText}"
  let some value := valueText.toNat? | throw s!"Bad value {valueText}"
  let sizes := [1, 3, 10, 30, 100]
  let allowed := (sizes.zipIdx).filterMap fun (size, index) =>
    if (mask / (2 ^ index)) % 2 == 1 then some size else none
  let unit := 10 ^ 16
  let catalog := poolsFor .mainnet (some "ETH")
  let selected := catalog.filter fun pool => allowed.contains (pool.amount / unit)
  let result := requireDenominationPlan (value * unit) selected
  match status, result with
  | "error", .error _ => return (mask, value, false)
  | "ok", .ok plan =>
      let actual := String.intercalate ";" (plan.entries.map fun entry =>
        s!"{entry.pool.denomination}:{entry.count}")
      if actual != entryText then throw s!"Mismatch {mask}/{value}: {actual} vs {entryText}"
      if !(validatePlan (value * unit) selected plan).isOk then
        throw s!"Native plan accounting validator rejected {mask}/{value}"
      if (validatePlan (value * unit) selected { plan with noteCount := plan.noteCount + 1 }).isOk then
        throw s!"Native plan accounting validator accepted a changed count at {mask}/{value}"
      return (mask, value, true)
  | _, _ => throw s!"Status mismatch {mask}/{value}: {status}"

def main : IO UInt32 := do
  let data ← IO.FS.readFile "fixtures/plan-grid.csv"
  let mut count := 0
  let mut accepted := 0
  let mut seen : List (Nat × Nat) := []
  for line in data.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match checkLine line with
    | .ok (mask, value, isPlan) =>
        if seen.contains (mask, value) then
          IO.eprintln s!"Duplicate fixture cell {mask}/{value}"
          return 1
        seen := (mask, value) :: seen
        count := count + 1
        if isPlan then accepted := accepted + 1
    | .error error =>
        IO.eprintln error
        return 1
  if count != 1860 then
    IO.eprintln s!"Expected 1860 cases, found {count}"
    return 1
  for mask in [1:32] do
    for value in [1:61] do
      if !seen.contains (mask, value) then
        IO.eprintln s!"Missing fixture cell {mask}/{value}"
        return 1
  IO.println s!"PASS: checked {count} pinned denomination-plan cases (31 catalogs × 60 amounts; {accepted} exact plans, {count - accepted} rejections)"
  return 0
