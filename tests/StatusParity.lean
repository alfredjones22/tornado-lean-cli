import Lean
import Tornado.Domain.Status

open Lean Tornado.Domain

def main : IO UInt32 := do
  let input ← IO.FS.readFile "fixtures/status-parity.json"
  let .ok root := Json.parse input | return 1
  let .ok cases := (root.getObjVal? "cases").bind Json.getArr? | return 1
  let mut matched := 0
  for item in cases do
    let .ok name := (item.getObjVal? "name").bind Json.getStr? | return 1
    let .ok raw := (item.getObjVal? "raw").bind Json.getStr? | return 1
    let .ok accepted := (item.getObjVal? "accepted").bind Json.getBool? | return 1
    let actual := (decodeWithdrawalStatus raw).isOk
    if actual != accepted then
      IO.eprintln s!"MISMATCH {name}: TS={accepted} Lean={actual}"
    else
      matched := matched + 1
  IO.println s!"Matched {matched}/{cases.size} TS status JSON oracle cases"
  return if matched == cases.size then 0 else 1
