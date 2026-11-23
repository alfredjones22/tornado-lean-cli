import Tornado.Cli.NullifierSpent

namespace Tornado.Cli.NullifierSpent.Test

open Lean Tornado.Domain Tornado.Runtime
open Tornado.Cli.NullifierSpent

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def rejects (action : IO α) (message : String) : IO Unit := do
  let mut didReject := false
  try
    let _ ← action
  catch _ => didReject := true
  require didReject message

def main : IO UInt32 := do
  try
    let pool := (poolsFor .mainnet).head!
    let hash := ByteArray.mk (Array.replicate 32 (0xab : UInt8))
    let selected : Selection := ⟨.mainnet, pool, hash, 16⟩
    require (validSelection selected) "Catalogued selection was rejected."
    let params ← unwrap (callParams selected)
    require (params.size == 2) "eth_call parameter count changed."
    require ((← unwrap (← unwrap (params[0]!.getObjVal? "to")).getStr?) == pool.address)
      "eth_call target is not the selected pool."
    let expectedData := "0xe5285dcc" ++ String.join (List.replicate 32 "ab")
    require ((← unwrap (← unwrap (params[0]!.getObjVal? "data")).getStr?) == expectedData)
      "isSpent calldata differs from viem's selector or bytes32 argument."
    require ((← unwrap params[1]!.getStr?) == "0x10")
      "eth_call does not use the selected exact numeric block."
    require ((← unwrap (decodeBool (toJson trueWord))) == true)
      "Canonical ABI true was not accepted."
    require ((← unwrap (decodeBool (toJson falseWord))) == false)
      "Canonical ABI false was not accepted."
    for value in ["0x1", "0x0", "0x", "0x02", "0X" ++ String.ofList (List.replicate 64 '0'),
        "0x" ++ String.ofList (List.replicate 63 '0') ++ "2"] do
      require (!(decodeBool (toJson value)).isOk)
        "Malformed or noncanonical ABI bool was accepted."
    require (!(decodeBool Json.null).isOk) "Null RPC result was accepted."
    let wrongChain := { selected with chainId := .sepolia }
    require (!(validateSelection wrongChain).isOk) "Pool from another chain was accepted."
    let forgedPool := { pool with denomination := "12345" }
    require (!(validateSelection { selected with pool := forgedPool }).isOk)
      "Forged catalog row was accepted."
    require (!(validateSelection { selected with nullifierHash := hash.extract 0 31 }).isOk)
      "Short nullifier hash was accepted."
    require (!(validateSelection { selected with blockNumber := 2 ^ 256 }).isOk)
      "Out-of-range selected block was accepted."

    let fetch : JsonRpc.Method → Array Json → IO Json := fun method arguments =>
      match method with
      | .chainId => pure (toJson ("0x1" : String))
      | .blockNumber => pure (toJson ("0x10" : String))
      | .call => do
          require (arguments == params) "RPC read changed the selected pool, hash, or block."
          pure (toJson trueWord)
      | _ => throw <| IO.userError "Unexpected RPC method."
    require (← checkWith selected fetch) "Exact spent response was not accepted."
    let unspent : JsonRpc.Method → Array Json → IO Json := fun method arguments =>
      if method == .call then pure (toJson falseWord) else fetch method arguments
    require (!(← checkWith selected unspent)) "Canonical unspent response was not accepted."
    let differentChain : JsonRpc.Method → Array Json → IO Json := fun method arguments =>
      if method == .chainId then pure (toJson ("0xaa" : String)) else fetch method arguments
    rejects (checkWith selected differentChain) "Wrong RPC chain reached isSpent."
    let behind : JsonRpc.Method → Array Json → IO Json := fun method arguments =>
      if method == .blockNumber then pure (toJson ("0xf" : String)) else fetch method arguments
    rejects (checkWith selected behind) "RPC head behind selected block was accepted."
    let malformed : JsonRpc.Method → Array Json → IO Json := fun method arguments =>
      if method == .call then pure (toJson ("0x02" : String)) else fetch method arguments
    rejects (checkWith selected malformed) "Malformed RPC bool became a spent answer."
    let failed : JsonRpc.Method → Array Json → IO Json := fun method arguments =>
      if method == .call then throw <| IO.userError "endpoint failed" else fetch method arguments
    rejects (checkWith selected failed) "RPC failure became a spent answer."
    let queried ← IO.mkRef false
    let noFetch : JsonRpc.Method → Array Json → IO Json := fun _ _ => do
      queried.set true
      pure .null
    rejects (checkWith wrongChain noFetch) "Invalid selection reached the RPC."
    require (!(← queried.get)) "Invalid selection performed an RPC request."
    IO.println "PASS: exact-block nullifier-spent selection, ABI, and RPC checks"
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)

end Tornado.Cli.NullifierSpent.Test

def main : IO UInt32 := Tornado.Cli.NullifierSpent.Test.main
