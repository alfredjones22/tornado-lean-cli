import Tornado.Protocol.RpcHistory

namespace Tornado.Protocol.RpcHistoryTests

open Lean Tornado.Protocol.RpcHistory Tornado.Protocol.SagaHistory

private def read (name : String) : IO String := do
  let root := (← IO.getEnv "TORNADO_SAGA_FIXTURES").getD "fixtures/saga-history/"
  let bytes ← IO.FS.readBinFile (root ++ name)
  let some raw := String.fromUTF8? bytes
    | throw <| IO.userError s!"{name}: not UTF-8"
  return raw

private def require (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"{name}: assertion failed"

private def success (name : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{name}: {message}"

private def failure (name : String) (value : Except String α) : IO Unit :=
  match value with
  | .ok _ => throw <| IO.userError s!"{name}: unexpectedly accepted"
  | .error _ => pure ()

private def parseFixture (selection : Selection) (name : String) :
    IO (Except String CheckedSlice) := do
  pure <| parseRange selection 102 108 7 8
    (← read (name ++ "-chain.json")) (← read (name ++ "-logs.json"))

def main : IO Unit := do
  let selection : Selection := {
    chainId := 1, pool := 170, registeredBlock := 100,
    lastSyncedBlock := 103, finalizedBlock := some 102, head := 108 }
  let params ← success "valid request" (requestParams selection 102 108)
  require "one filter" (params.size == 1)
  let filter := params[0]!
  require "pool address" ((filter.getObjValAs? String "address").toOption ==
    some ("0x" ++ String.ofList (List.replicate 38 '0') ++ "aa"))
  require "canonical from" ((filter.getObjValAs? String "fromBlock").toOption == some "0x66")
  require "canonical to" ((filter.getObjValAs? String "toBlock").toOption == some "0x6c")
  failure "request before registration" (requestParams selection 99 108)
  failure "request past captured head" (requestParams selection 102 109)
  failure "inverted request" (requestParams selection 108 107)
  let valid ← success "valid logs" (← parseFixture selection "rpc-valid")
  require "two valid logs" (valid.events.size == 2 && valid.events[0]!.isDeposit &&
    !valid.events[1]!.isDeposit)
  for name in #["rpc-wrong-chain", "rpc-wrong-pool", "rpc-out-of-range",
      "rpc-reordered", "rpc-removed", "rpc-malformed-abi"] do
    failure name (← parseFixture selection name)
  IO.println "RPC history: 14 offline fixture assertions passed"

end Tornado.Protocol.RpcHistoryTests

def main : IO Unit := Tornado.Protocol.RpcHistoryTests.main
