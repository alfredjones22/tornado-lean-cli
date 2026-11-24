import Tornado.Runtime.WithdrawalJournalProgram

namespace Tornado.Test.WithdrawalJournalProgram

open Tornado.Runtime.WithdrawalJournalProgram

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def emptyStore : Physical.Store := fun _ => none

private def put (before : Physical.Store) (path : String) (data : ByteArray) : Physical.Store :=
  fun query => if query = path then some data.data else before query

private def paths : Array String := #["/private/mirror-a", "/private/mirror-b", "/private/mirror-c"]
private def initialBytes := "canonical original signed payload".toUTF8
private def finalBytes := "canonical next signed payload".toUTF8

private def canAcknowledge {program : Program} (report : Report program) : IO Bool := do
  try
    let receipt ← requireSuccess report
    require (receipt.trace.length == program.length) "An acknowledgement omitted dispatched commands."
    pure true
  catch _ => pure false

private def scenario (replace lost : Bool) (fault : Nat) : IO Unit := do
  let before : Physical.Store := if replace then
      paths.foldl (fun store path => put store path initialBytes) emptyStore
    else emptyStore
  let before := put before "/private/unrelated" (ByteArray.mk #[7, 8])
  let store ← IO.mkRef before
  let issued ← IO.mkRef (#[] : Array Command)
  let perform (command : Command) : IO Unit := do
    let index := (← issued.get).size
    issued.modify (·.push command)
    if index == fault && !lost then throw <| IO.userError "failed before write"
    let after ← checked <| Physical.apply command (← store.get)
    store.set after
    if index == fault && lost then throw <| IO.userError "completed write, lost reply"
  let effects : Effects := {
    createPrivate := fun path bytes => perform (.create path bytes),
    replacePrivate := fun path previous bytes => perform (.replace path previous bytes) }
  let program := paths.toList.map (fun path => if replace then
    Command.replace path initialBytes finalBytes else .create path finalBytes)
  let report ← runIO effects program
  let failed := fault < paths.size
  let completed := if failed then fault else paths.size
  let attempted := if failed then fault + 1 else paths.size
  require (report.stopped == failed && report.completedCommands.length == completed &&
    report.trace.length == attempted && (← issued.get).size == attempted)
    "Failure did not stop at the exact original command prefix."
  require ((← issued.get).toList == program.take attempted)
    "Actual dispatch reordered, omitted, or substituted a file command."
  require ((← canAcknowledge report) == !failed)
    "A failed/lost reply authorized complete journal acknowledgement."
  let after ← store.get
  for index in [0:paths.size] do
    let changed := index < completed || (failed && lost && index == fault)
    let expected := if changed then some finalBytes.data
      else if replace then some initialBytes.data else none
    require (after paths[index]! == expected)
      "The final physical store did not retain the exact possible completed prefix."
  require (after "/private/unrelated" == some #[7, 8]) "The program changed an unrelated file."

private def partialCreate : IO Unit := do
  let fragment := ByteArray.mk #[0x7b, 0x22]
  let store ← IO.mkRef (put emptyStore paths[0]! fragment)
  let attempts ← IO.mkRef (0 : Nat)
  let effects : Effects := {
    createPrivate := fun path bytes => do
      attempts.modify (· + 1)
      let after ← checked <| Physical.apply (.create path bytes) (← store.get)
      store.set after,
    replacePrivate := fun _ _ _ => throw <| IO.userError "Unexpected replace" }
  let program := paths.toList.map (fun path => Command.create path finalBytes)
  let report ← runIO effects program
  require (report.stopped && report.completedCommands.isEmpty && (← attempts.get) == 1 &&
    !(← canAcknowledge report)) "An incomplete crash claim permitted readmission or exposure."
  require ((← store.get) paths[0]! == some fragment.data)
    "Readmission overwrote an incomplete claim."

private def staleCAS : IO Unit := do
  let rival := "concurrent protected status evidence".toUTF8
  let store ← IO.mkRef (put emptyStore paths[0]! rival)
  let effects : Effects := {
    createPrivate := fun _ _ => throw <| IO.userError "Unexpected create",
    replacePrivate := fun path previous next => do
      let after ← checked <| Physical.apply (.replace path previous next) (← store.get)
      store.set after }
  let report ← runIO effects [.replace paths[0]! initialBytes finalBytes]
  require (report.stopped && !(← canAcknowledge report) &&
    (← store.get) paths[0]! == some rival.data) "A stale CAS erased concurrent status evidence."

def main : IO Unit := do
  for replace in #[false, true] do
    for lost in #[false, true] do
      for fault in [0:4] do scenario replace lost fault
  partialCreate
  staleCAS
  IO.println "PASS: 18 finite journal program scenarios, exact command/byte prefixes, every before-write/lost-reply cut, partial-claim readmission block, and stale CAS preservation"

end Tornado.Test.WithdrawalJournalProgram

def main : IO Unit := Tornado.Test.WithdrawalJournalProgram.main
