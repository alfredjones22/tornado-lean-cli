import Tornado.Cli.WithdrawOne

namespace Tornado.Cli.WithdrawOne.Test

open Lean Tornado.Domain Tornado.Cli.WithdrawOne

private def require (label : String) (value : Bool) : IO Unit :=
  unless value do throw <| IO.userError s!"{label}: assertion failed"

private def checked (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def expectFailure (label : String) (value : IO α) : IO Unit := do
  let failed ← try
      let _ ← value
      pure false
    catch _ => pure true
  require label failed

private def fixtureNote : String :=
  "tornado-eth-0.01-1-0x33567fb6463d588b0ef7ff2d415130e0d91059781005f504671ddc3f03c4adc8b873cfa627a16e46d1f33b81d9c7e86772a083575ccccb9104ed77057b53"

private def statusName : String :=
  "tornado-withdraw-1-b92ae0e9fa6851991dd9cbb1e4d1736fee0f92691b0c27a51edce9c4ef055fff.json"

private def fakeReport (note : BackupIdentity) (spent : Bool)
    (address commitment : String) (checkedBlock depositBlock : String) : String :=
  (Json.mkObj [
    ("pool", Json.mkObj [("address", toJson address)]),
    ("commitment", toJson commitment),
    ("checked", Json.mkObj [
      ("blockNumber", toJson checkedBlock), ("spent", toJson spent)]),
    ("deposit", Json.mkObj [("blockNumber", toJson depositBlock)]),
    ("nullifierHash", if spent then toJson note.publicIdentity.nullifierHash else Json.null)]).compress

def main : IO Unit := do
  let selected := (← checked "backup" (parseDepositBackup fixtureNote .mainnet)).head!
  let name ← checked "opaque status filename" (statusFileName selected.note)
  require "HMAC-SHA256 status parity" (name == statusName)
  require "filename does not expose nullifier hash"
    (!name.contains selected.publicIdentity.nullifierHash &&
      !name.contains selected.note.preimage)
  let checksum ← checked "valid checksum" (checkedRecipient
    "0x52908400098527886E0F7030069857D2E4169EE7")
  let lower ← checked "lowercase address" (checkedRecipient
    "0x52908400098527886e0f7030069857d2e4169ee7")
  require "EIP-55 canonical address" (checksum == lower &&
    checksum == "0x52908400098527886E0F7030069857D2E4169EE7")
  require "wrong mixed-case checksum rejected"
    (!(checkedRecipient "0x52908400098527886E0F7030069857D2E4169Ee7").isOk)
  require "zero recipient rejected"
    (!(checkedRecipient "0x0000000000000000000000000000000000000000").isOk)
  let recipient ← checked "recipient" (checkedRecipient
    "0x00000000000000000000000000000000000000cc")
  let statusPath := "/tmp/withdraw-review/" ++ name
  let dry := dryRunReview selected recipient statusPath "public.pimlico.io" "4337"
  require "exact direct dry-run review" (dry ==
    s!"Route: 4337 paymaster\nRecipient: {recipient}\nPool: 0.01 ETH ({selected.note.pool.address})\nNote value: 0.01 ETH\nBundler host: public.pimlico.io\nStatus file if submitted: {statusPath}\nDry run complete. No proof, fee quote, signature or UserOperation was created.\n")
  require "dry-run hides note secret and nullifier" (!dry.contains selected.note.preimage &&
    !dry.contains selected.publicIdentity.nullifierHash)
  let relayer := dryRunReview selected recipient statusPath "unused" "relayer"
  require "relayer review omits bundler" (relayer.startsWith "Route: Classic TORN relayer\n" &&
    !relayer.contains "Bundler host:")
  let report := fakeReport selected false selected.note.pool.address
    selected.publicIdentity.commitment "26200000" "26198980"
  let preflight ← checked "preflight summary"
    (preflightSummary selected recipient statusPath "public.pimlico.io" "4337" report)
  require "unspent preflight" (preflight.contains "Deposit verified at block 26198980." &&
    preflight.contains "Unspent at checked block 26200000." &&
    !preflight.contains selected.note.preimage)
  require "spent preflight rejected" (!(preflightSummary selected recipient statusPath
    "public.pimlico.io" "4337" (fakeReport selected true selected.note.pool.address
      selected.publicIdentity.commitment "26200000" "26198980")).isOk)
  require "wrong pool preflight rejected" (!(preflightSummary selected recipient statusPath
    "public.pimlico.io" "4337" (fakeReport selected false
      "0x0000000000000000000000000000000000000001" selected.publicIdentity.commitment
      "26200000" "26198980")).isOk)
  require "wrong commitment preflight rejected" (!(preflightSummary selected recipient statusPath
    "public.pimlico.io" "4337" (fakeReport selected false selected.note.pool.address
      "0x0000000000000000000000000000000000000000000000000000000000000001"
      "26200000" "26198980")).isOk)
  require "future deposit preflight rejected" (!(preflightSummary selected recipient statusPath
    "public.pimlico.io" "4337" (fakeReport selected false selected.note.pool.address
      selected.publicIdentity.commitment "26198979" "26198980")).isOk)
  let help ← withdrawOneCommand ["--help"]
  require "runnable command help" (help.startsWith "Usage: tornado withdraw one")
  expectFailure "no-flag send fails closed" (withdrawOneCommand [])
  expectFailure "invalid route fails before private read"
    (withdrawOneCommand ["--dry-run", "--route", "invalid"])
  expectFailure "conflicting modes fail closed"
    (withdrawOneCommand ["--dry-run", "--preflight"])
  IO.println "PASS: protected-note withdrawal review, EIP-55 recipient, opaque HMAC status path, and read-only preflight gates"

end Tornado.Cli.WithdrawOne.Test

def main : IO Unit := Tornado.Cli.WithdrawOne.Test.main
