import Tornado.Runtime.AttemptJournal

/-!
Compiled OS-boundary exercise for the journal replay refinement. This is a
local disposable fixture with public hashes, never a funded note or network
operation. The JavaScript harness controls write permissions and races two
processes; this binary performs the same native journal operations as a CLI
caller would.
-/

namespace Tornado.Tests.JournalIORefinement

open Tornado.Runtime.AttemptJournal

private def hash (c : Char) : String :=
  "0x" ++ String.ofList (List.replicate 64 c)

private def prepared (directory id : String) : IO Unit := do
  let _ ← start directory id .direct (hash 'a') [hash 'b']
  let _ ← append directory id .direct (.sign (hash 'a'))
  let state ← append directory id .direct (.reserve (hash 'b'))
  unless state.direct.phase == .reserved && state.direct.sends == 0 &&
      state.nextSeq == 3 do
    throw <| IO.userError "Prepared journal is not durably reserved."

private def snapshot (directory id : String) : IO Unit := do
  let state ← load directory id .direct
  if state.direct.phase == .reserved && state.direct.sends == 0 &&
      state.nextSeq == 3 then
    IO.println "reserved:0"
  else if state.direct.phase == .exposed && state.direct.sends == 0 &&
      state.nextSeq == 4 then
    IO.println "exposed:0"
  else if state.direct.phase == .submitted && state.direct.sends == 1 &&
      state.nextSeq == 5 then
    IO.println "submitted:1"
  else
    throw <| IO.userError "Recovered journal has unexpected phase or send count."

def main (args : List String) : IO Unit := do
  match args with
  | ["prepare", directory, id] =>
      prepared directory id
      IO.println "prepared"
  | ["arm", directory, id] =>
      let state ← armSubmission directory id .direct
      unless state.direct.phase == .submitted && state.direct.sends == 1 do
        throw <| IO.userError "Arming did not consume one send slot."
      IO.println "armed"
  | ["expose", directory, id] =>
      let state ← append directory id .direct .expose
      unless state.direct.phase == .exposed && state.direct.sends == 0 do
        throw <| IO.userError "Exposure intent was not durable."
      IO.println "exposed"
  | ["replay", directory, id] => snapshot directory id
  | _ => throw <| IO.userError "Usage: journal_refinement_test <prepare|arm|expose|replay> <dir> <id>"

end Tornado.Tests.JournalIORefinement

def main (args : List String) : IO Unit :=
  Tornado.Tests.JournalIORefinement.main args
