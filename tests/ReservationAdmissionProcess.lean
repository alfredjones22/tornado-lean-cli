import Tornado.Runtime.ReservationAdmission
import Tornado.Runtime.ProtectedIO

open Tornado.Runtime.ReservationAdmission Tornado.Runtime.ProtectedIO

@[extern "tornado_test_fault_arm"]
opaque armTestFault (mode : UInt32) : IO Unit

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def rejected (action : IO α) : IO Bool := do
  try let _ ← action; return false
  catch _ => return true

private def oldBytes : ByteArray :=
  "{\"phase\":\"reserved\",\"signedPayload\":\"public-synthetic-fixed-payload\",\"releaseReservations\":false}\n".toUTF8

private def newBytes : ByteArray :=
  "{\"phase\":\"exposed\",\"signedPayload\":\"public-synthetic-fixed-payload\",\"releaseReservations\":false}\n".toUTF8

private def child (mode : Nat) (path : String) : IO Unit := do
  armTestFault mode.toUInt32
  if mode <= 2 then createPrivate path oldBytes
  else replacePrivate path oldBytes newBytes
  throw <| IO.userError "The process fault did not fire."

private def parent (base : String) : IO Unit := do
  let executable ← IO.appPath
  for mode in [1:6] do
    let path := base ++ s!"/claim-{mode}"
    if mode > 2 then createPrivate path oldBytes
    let output ← IO.Process.output {
      cmd := executable.toString, args := #["child", toString mode, path] }
    require (output.exitCode == (80 + mode).toUInt32)
      s!"Wrong process cut boundary: mode {mode}; exit {output.exitCode}; {output.stderr}"
    let actual ← readPrivate path
    if mode == 1 then
      require (actual.size == 16 && actual != oldBytes)
        "Mid-write crash failed to retain a real partial occupied claim."
    else if mode == 4 then
      require (actual == newBytes) "Post-rename parent-sync crash lost the new exact journal."
    else
      require (actual == oldBytes) "Process cut changed the original reserved journal unexpectedly."
    require (← rejected <| requireUnclaimed #[path])
      "Real partial or committed claim passed native readmission."
    require (← rejected <| createPrivate path newBytes)
      "Competing route exclusive creation overwrote an occupied real claim."
    if mode > 2 then
      let lock := base ++ s!"/.claim-{mode}.tornado-lock"
      require (← entryExists lock) "Replacement crash did not leave its actual exclusive sidecar."
      require (← rejected <| replacePrivate path actual oldBytes)
        "A crash-stale replacement lock permitted another CAS."
      if mode == 4 then
        -- Explicit test cleanup after inspecting exact new bytes, not runtime
        -- automatic recovery. The old expectation must still fail without it.
        removePrivateExact lock ByteArray.empty
        require (← rejected <| replacePrivate path oldBytes oldBytes)
          "Removing a stale sidecar allowed stale expected bytes to overwrite the committed journal."
        require ((← readPrivate path) == newBytes) "Stale CAS changed a committed journal."
  IO.println "PASS: 5 real protected-I/O process cuts, partial and committed-lost-reply readmission, exclusive-create route exclusion, stale-lock and stale-byte CAS"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["child", mode, path] =>
      let some number := mode.toNat? | throw <| IO.userError "Invalid synthetic child mode."
      child number path
    | [base] => parent base
    | _ => throw <| IO.userError "Pass an existing protected test directory."
    return 0
  catch error => IO.eprintln error.toString; return 1
