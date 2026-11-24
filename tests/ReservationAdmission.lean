import Tornado.Runtime.ReservationAdmission

open Tornado.Runtime.ReservationAdmission

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def rejects (action : IO α) : IO Bool := do
  try let _ ← action; return false
  catch _ => return true

private def faultCase (paths : Array String) (index : Nat) (lostReply : Bool) : IO Unit := do
  let calls ← IO.mkRef (#[] : Array String)
  let effects : Effects := ⟨fun path => do
    calls.modify (·.push path)
    if path == paths[index]! then
      if lostReply then throw <| IO.userError "Synthetic query completed, but its reply was lost."
      return true
    return false⟩
  let report ← runWith effects paths.toList
  ensure (report.outcome == .blocked && report.trace.length == index + 1 &&
    (← calls.get) == paths.extract 0 (index + 1)) "Reservation query continued after a present or failed observation."
  ensure (← rejects <| requireUnclaimedWith effects paths) "A present or failed query minted an absence certificate."

def main : IO Unit := do
  let paths := (List.range 12).toArray.map (fun i => s!"/opaque/tornado-withdraw-1-{i}.json")
  let called ← IO.mkRef (#[] : Array String)
  let absent : Effects := ⟨fun path => do called.modify (·.push path); return false⟩
  let checked ← requireUnclaimedWith absent paths
  ensure ((← called.get) == paths && checked.report.outcome == .allAbsent)
    "Admission failed to observe every exact opaque path once."
  for index in [0:paths.size] do
    faultCase paths index false
    faultCase paths index true
  let invalidCalled ← IO.mkRef (0 : Nat)
  let never : Effects := ⟨fun _ => do invalidCalled.modify (· + 1); return false⟩
  for invalid in #[#[], paths.push "/extra", #[paths[0]!, paths[0]!], #["relative"],
      #["/" ++ String.ofList (List.replicate 4096 'x')]] do
    ensure (← rejects <| requireUnclaimedWith never invalid) "Invalid reservation path scope was accepted."
  ensure ((← invalidCalled.get) == 0) "Invalid reservation path scope queried the filesystem."
  -- Absence is intentionally not exclusivity: both routes can observe an
  -- absent path; only one subsequent exclusive create may succeed.
  let occupied ← IO.mkRef false
  let racing : Effects := ⟨fun _ => occupied.get⟩
  let one := #[paths[0]!]
  let _ ← requireUnclaimedWith racing one
  let _ ← requireUnclaimedWith racing one
  let createExclusive : IO Unit := do
    if ← occupied.get then throw <| IO.userError "Synthetic EEXIST"
    occupied.set true
  createExclusive
  ensure (← rejects createExclusive) "A competing route bypassed exclusive reservation."
  ensure (← rejects <| requireUnclaimedWith racing one) "Readmission ignored a partial reservation."
  -- Any file, even an empty undecodable partial claim, blocks native admission.
  let unique ← IO.monoNanosNow
  let directory := s!"/tmp/tornado-admission-native-review-{unique}"
  IO.FS.createDir directory
  let path := directory ++ "/partial.json"
  try
    let _ ← requireUnclaimed #[path]
    IO.FS.writeFile path ""
    ensure (← rejects <| requireUnclaimed #[path]) "Native admission ignored an empty partial file."
    IO.FS.writeFile path "{\"status\":\"rejected\",\"releaseReservations\":true}"
    ensure (← rejects <| requireUnclaimed #[path]) "Native admission treated status JSON as release permission."
    let link := directory ++ "/dangling-link"
    let linked ← IO.Process.output { cmd := "/bin/ln", args := #["-s", directory ++ "/missing", link] }
    ensure (linked.exitCode == 0) "Failed to create a synthetic dangling symlink."
    ensure (← rejects <| requireUnclaimed #[link]) "Native admission followed a dangling symlink and reported absence."
    let tooLong := directory ++ "/" ++ String.ofList (List.replicate 300 'x')
    ensure (← rejects <| requireUnclaimed #[tooLong]) "Native admission suppressed a metadata error as absence."
  finally IO.FS.removeDirAll directory
  IO.println "PASS: exact absent query traces, 24 stop/fail-closed query faults, 5 scope guards, route race, partial file, symlink/error and status-independent readmission"
