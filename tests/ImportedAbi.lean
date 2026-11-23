import Tornado.Cli.WithdrawBatch

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol
open Tornado.Cli.WithdrawBatch

private def checked (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def field (value : Json) (name : String) : IO Json :=
  checked name <| value.getObjVal? name

private def text (value : Json) (name : String) : IO String := do
  checked name <| (← field value name).getStr?

private def chain (value : Json) : IO ChainId := do
  let number ← checked "chainId" <| (← field value "chainId").getNat?
  let some chain := chainFromNat number | throw <| IO.userError "Invalid fixture chain."
  return chain

def main : IO UInt32 := do
  let fixture ← checked "fixture JSON" <| Json.parse
    (← IO.FS.readFile "fixtures/imported-abi-vectors.json")
  let cases ← checked "cases" <| (← field fixture "cases").getArr?
  let rejected ← checked "rejection cases" <| (← field fixture "rejectionCases").getArr?
  for row in cases do
    let name ← text row "name"
    let input ← field row "input"
    let calls ← checked name <| parseContractCalls input.compress (← chain row)
    let expected ← checked "expected calls" <| (← field row "calls").getArr?
    require (calls.size == expected.size) s!"{name}: call count changed."
    for i in [0:calls.size] do
      let expectedCall := expected[i]!
      let address ← checked "expected address" <| parseHexBytes (← text expectedCall "to")
      let target := address.data.foldl (fun n byte => n * 256 + byte.toNat) 0
      let some amount := (← text expectedCall "value").toNat?
        | throw <| IO.userError "Invalid expected value."
      let data ← checked "expected calldata" <| parseHexBytes (← text expectedCall "data")
      require (calls[i]!.to == target && calls[i]!.value == amount && calls[i]!.data == data)
        s!"{name}: native method encoding differs from pinned TypeScript/viem calldata."
    let expectedHash ← checked "expected call hash" <| parseHexBytes (← text row "callsHash")
    require ((← checked "native call hash" <| Abi.callsHash calls) == expectedHash)
      s!"{name}: ordered call hash differs from pinned TypeScript."
  for row in rejected do
    let name ← text row "name"
    let input ← field row "input"
    require (!(parseContractCalls input.compress (← chain row)).isOk)
      s!"{name}: malformed ABI import was accepted."
  let nonSolidityType := Json.mkObj [
    ("name", toJson ("run" : String)),
    ("inputs", Json.arr #[Json.mkObj [
      ("name", toJson ("value" : String)), ("type", toJson ("uint7" : String))]])]
  require (!(ImportedAbi.encodeFunctionData nonSolidityType
    (Json.mkObj [("value", toJson ("1" : String))]) 0).isOk)
    "A non-Solidity integer width was accepted."
  IO.println s!"PASS: {cases.size} pinned Safe ABI encoding/hash cases, {rejected.size} import rejections, and bounded Solidity types"
  return 0
