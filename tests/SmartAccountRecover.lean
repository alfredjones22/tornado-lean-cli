import Tornado.Cli.SmartAccountRecover

namespace Tornado.Cli.SmartAccountRecover.Test

open Lean Tornado.Domain Tornado.SmartAccount Tornado.Runtime
open Tornado.Cli.SmartAccountRecover

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def addressNat (raw : String) : IO Nat := do
  let bytes ← unwrap (parseHexBytes raw)
  require (bytes.size == 20) "Fixture address is not 20 bytes."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def field (json : Json) (name : String) : IO Json :=
  unwrap (json.getObjVal? name)

private def string (json : Json) (name : String) : IO String := do
  unwrap (← field json name).getStr?

private def contains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def rejects (action : IO α) (message : String) : IO Unit := do
  let mut didReject := false
  try
    let _ ← action
  catch _ => didReject := true
  require didReject message

def main : IO UInt32 := do
  try
    let root ← unwrap (Json.parse (← IO.FS.readFile "fixtures/recovery-vectors.json"))
    let vectors ← unwrap (← field root "vectors").getArr?
    let first := vectors[0]!
    let owner ← addressNat (← string first "owner")
    let accountAddress ← addressNat (← string first "account")
    let receiver ← addressNat (← string first "recipient")
    let rawBalances ← unwrap (← field first "balances").getArr?
    let mut balances := #[]
    for item in rawBalances do
      let raw ← unwrap item.getStr?
      let some amount := raw.toNat?
        | throw <| IO.userError "Invalid fixture balance."
      balances := balances.push amount
    let some deposit := (← string first "entryPointDeposit").toNat?
      | throw <| IO.userError "Invalid fixture EntryPoint deposit."
    let plan ← unwrap (planRecovery .mainnet owner accountAddress receiver balances deposit)
    let account : Tornado.Cli.SmartAccountShow.Account :=
      ⟨owner, accountAddress, true, 42⟩
    let review : Review := ⟨.mainnet, 12345, account, plan⟩
    let output ← unwrap (render review)
    require (output.startsWith "Owner: " && contains output "Recover " &&
      contains output "Calls: " && contains output "Block: 12345" &&
      output.endsWith "No recovery transaction was signed or submitted.\n")
      "Recovery review omitted checked balances, calls, or dry-run warning."
    require (contains output (← string first "data"))
      "Recovery review omitted exact checked account calldata."
    require (!(render { review with account := { account with address := accountAddress + 1 } }).isOk)
      "Review accepted a plan for another smart account."
    require (!(render { review with plan := { plan with data := ByteArray.empty } }).isOk)
      "Review accepted calldata different from its call list."

    let help ← recoverCommand ["--help"]
    require (help.startsWith "Usage: tornado smart-account recover --owner <address> --dry-run")
      "Safe recovery help changed."
    -- Omitted account sources now use the native terminal prompt. Its no-TTY
    -- and file errors are tested by the compiled CLI and signer suites.
    let noOwner ← try
      let _ ← recoverCommand ["--dry-run", "--non-interactive"]
      pure ""
    catch error => pure error.toString
    require (noOwner == "--non-interactive requires --owner or --owner-key-file for recovery review.")
      "Unattended recovery review attempted to prompt for an unspecified owner key."
    rejects (recoverCommand ["--owner", "0x1111111111111111111111111111111111111111"])
      "Recovery without --dry-run reached the RPC."
    rejects (recoverCommand ["--owner", "0x1111111111111111111111111111111111111111",
      "--dry-run", "--yes"]) "Send authorization was accepted by the planner."

    let calls ← IO.mkRef ([] : List JsonRpc.Method)
    let wrongChain : JsonRpc.Method → Array Json → IO Json := fun method _ => do
      calls.modify (· ++ [method])
      if method == .chainId then pure (toJson ("0xaa" : String))
      else throw <| IO.userError "Wrong chain should stop before other RPC calls."
    rejects (inspectWith .mainnet owner receiver wrongChain)
      "Wrong RPC chain yielded a recovery plan."
    require ((← calls.get) == [.chainId])
      "Wrong RPC chain did not stop before identity or balance reads."
    let noFactory : JsonRpc.Method → Array Json → IO Json := fun method _ => do
      calls.modify (· ++ [method])
      match method with
      | .chainId => pure (toJson ("0x1" : String))
      | .blockNumber => pure (toJson ("0x2a" : String))
      | .getCode => pure (toJson ("0x" : String))
      | _ => throw <| IO.userError "Absent factory should stop before other RPC calls."
    calls.set []
    rejects (inspectWith .mainnet owner receiver noFactory)
      "Missing pinned factory yielded a recovery plan."
    require ((← calls.get) == [.chainId, .blockNumber, .getCode])
      "Factory guard did not stop before balance reads."
    IO.println "PASS: native smart-account recovery dry-run plan and fail-closed RPC guards"
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)

end Tornado.Cli.SmartAccountRecover.Test

def main : IO UInt32 := Tornado.Cli.SmartAccountRecover.Test.main
