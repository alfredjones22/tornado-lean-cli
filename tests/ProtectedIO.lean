import Tornado.Runtime.ProtectedIO

open Tornado.Runtime.ProtectedIO

private def ensure (condition : Bool) (description : String) : IO Unit :=
  unless condition do throw <| IO.userError description

private def failed (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

def main (args : List String) : IO Unit := do
  let base ← match args[0]? with
    | some path => pure path
    | none => throw <| IO.userError "Missing protected IO test directory"
  let content := "private Tornado test data\n".toUTF8
  if args[1]? == some "acl" then
    ensure (← failed (createPrivate (base ++ "/acl-parent/private") content))
      "ACL-bearing parent allowed private creation"
    ensure (← failed (readPrivate (base ++ "/acl-leaf")))
      "ACL-bearing private file was accepted"
    IO.println "Protected IO: inherited and direct ACL checks passed"
    return
  let privatePath := base ++ "/private"
  createPrivate privatePath content
  ensure ((← readPrivate privatePath) == content) "Private file roundtrip failed"
  ensure ((← readPrivate (base ++ "/./private")) == content)
    "Current-directory component was rejected"
  let collision ← try
    createPrivate privatePath "replacement must not be written".toUTF8
    pure false
  catch error =>
    match error with
    | .alreadyExists filename code _ => pure (filename == some privatePath && code != 0)
    | _ => pure false
  ensure collision "Exclusive create lost its structured already-exists error and path"
  ensure ((← readPrivate privatePath) == content) "Existing file was overwritten"
  ensure (← failed (readPrivate (base ++ "/public"))) "Public file was accepted"
  ensure (← failed (readPrivate (base ++ "/hardlink"))) "Hard link was accepted"
  ensure (← failed (readPrivate (base ++ "/symlink"))) "Symbolic link was accepted"
  ensure (← failed (readPrivate (base ++ "/parent-symlink/private")))
    "Symbolic-link parent was accepted"
  ensure (← failed (readPrivate (base ++ "/../private"))) "Parent traversal was accepted"
  ensure (← failed (createPrivate (base ++ "/../escape") content))
    "Parent traversal create was accepted"
  IO.println "Protected IO: 10 roundtrip and unsafe-path checks passed"
