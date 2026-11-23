import Tornado.Runtime.ProtectedIO

open Tornado.Runtime.ProtectedIO

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def rejects (action : IO α) (message : String) : IO Unit := do
  let mut didReject := false
  try
    let _ ← action
  catch _ => didReject := true
  require didReject message

def main (args : List String) : IO UInt32 := do
  try
    let some base := args[0]?
      | throw <| IO.userError "Pass an existing owner-only test directory."
    let path := base ++ "/journal"
    let before := "{\"status\":\"prepared\"}\n".toUTF8
    let after := "{\"status\":\"confirmed\"}\n".toUTF8
    createPrivate path before
    replacePrivate path before after
    require ((← readPrivate path) == after) "Atomic replacement lost the new journal."
    rejects (replacePrivate path before before) "Stale CAS bytes overwrote the journal."
    require ((← readPrivate path) == after) "Stale CAS altered the journal."
    rejects (replacePrivate path after (ByteArray.mk (Array.replicate (1024 * 1024 + 1) 0)))
      "Oversized replacement was accepted."
    require ((← readPrivate path) == after) "Oversized update altered the journal."
    let lock := base ++ "/.journal.tornado-lock"
    createPrivate lock "busy".toUTF8
    rejects (replacePrivate path after before) "Existing replacement lock was bypassed."
    require ((← readPrivate path) == after) "Locked replacement altered the journal."
    rejects (removePrivateExact path before) "Stale exact removal deleted the journal."
    removePrivateExact lock "busy".toUTF8
    replacePrivate path after before
    require ((← readPrivate path) == before) "Lock release did not permit a safe update."
    removePrivateExact path before
    rejects (readPrivate path) "Exact removal left the private file readable."
    IO.println "PASS: protected atomic replace, stale CAS, bounds, and lock rejection"
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)
