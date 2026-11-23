import Tornado.Domain.Plan
open Tornado.Domain

def checkChoice (line : String) : Except String Unit := do
  let [chainText, symbol, amountText, status, expected] := line.splitOn ","
    | throw "Bad fixture line"
  let some chainNat := chainText.toNat? | throw "Bad chain"
  let some chain := chainFromNat chainNat | throw "Unsupported chain"
  let some amount := amountText.toNat? | throw "Bad amount"
  let actual := denominationPlanChoices amount (poolsFor chain (some symbol))
  match status, actual with
  | "error", .error _ => return ()
  | "ok", .ok plans =>
      let text := String.intercalate "|" (plans.map fun plan =>
        String.intercalate ";" (plan.entries.map fun entry =>
          s!"{entry.pool.denomination}:{entry.count}"))
      if text != expected then throw s!"Mismatch {chainNat}/{symbol}/{amount}: {text} vs {expected}"
  | _, _ => throw s!"Result kind changed {chainNat}/{symbol}/{amount}"

def main : IO UInt32 := do
  let data ← IO.FS.readFile "fixtures/plan-choices.csv"
  let mut count := 0
  for line in data.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match checkChoice line with
    | .ok _ => count := count + 1
    | .error error =>
        IO.eprintln error
        return 1
  if count != 900 then
    IO.eprintln s!"Expected 900 choice cases, found {count}"
    return 1
  IO.println s!"PASS: checked {count} pinned plan-choice cases across seven chain/asset catalogs"
  return 0
