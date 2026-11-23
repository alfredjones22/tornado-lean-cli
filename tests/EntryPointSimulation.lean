import Tornado.Protocol.EntryPointSimulation

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.UserOperation08 Tornado.Protocol.EntryPointSimulation

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def main : IO UInt32 := do
  let fixture ← checked <| Json.parse (← IO.FS.readFile "fixtures/entrypoint-simulation.json")
  let signature ← checked <| parseHexBytes ("0x" ++ String.ofList (List.replicate 128 '1') ++ "1b")
  let op : UserOperation := {
    sender := 1, nonce := 0, callData := ← checked (parseHexBytes "0x1234"),
    verificationGasLimit := 50000, callGasLimit := 100000, preVerificationGas := 100000,
    maxFeePerGas := 1000000000, maxPriorityFeePerGas := 100000000,
    paymaster := some 0xb0ffcdc890e969579d348f519a9c3920c2dd04a5,
    paymasterVerificationGasLimit := 450000, paymasterPostOpGasLimit := 50000,
    paymasterData := ← checked (parseHexBytes "0x1234"), signature }
  let encoded ← checked (handleOpsData op)
  let expectedBytes ← checked <| (← checked <| fixture.getObjVal? "handleOpsData").getStr?
  require (Bundler.dataHex encoded == expectedBytes) "handleOps ABI differs from pinned viem"
  let params ← checked (requestParams op)
  require (params.size == 2) "Invalid signed simulation request framing"
  let nullifier ← checked (Abi.uintWord 7)
  let expected : List Events.ExpectedWithdrawal := [{
    pool := 0x199112eb461ea7eec1d75b33343542e1d069b41c,
    recipient := 2, nullifierHash := nullifier,
    relayer := 0xb0ffcdc890e969579d348f519a9c3920c2dd04a5, fee := 1 }]
  let response ← checked (fixture.getObjVal? "response")
  let passed ← checked (parsePassed 1 op expected response)
  require (Bundler.dataHex passed.hash ==
    (← checked <| (← checked <| fixture.getObjVal? "hash").getStr?))
    "Simulation operation hash differs from pinned viem"
  let blocks ← checked response.getArr?
  let calls ← checked <| (← checked <| blocks[0]!.getObjVal? "calls").getArr?
  let logs ← checked <| (← checked <| calls[0]!.getObjVal? "logs").getArr?
  let change (call : Json) : Json := .arr #[blocks[0]!.setObjVal! "calls" (.arr #[call])]
  require (!(parsePassed 1 op expected (change
      (calls[0]!.setObjVal! "status" (toJson ("0x0" : String))))).isOk)
    "Failed simulation was accepted"
  require (!(parsePassed 1 op expected (change
      (calls[0]!.setObjVal! "logs" (.arr #[logs[0]!])))).isOk)
    "Missing selected pool withdrawal was accepted"
  require (!(parsePassed 1 op expected (change
      (calls[0]!.setObjVal! "logs" (.arr (logs.push logs[0]!))))).isOk)
    "Contradictory duplicate EntryPoint evidence was accepted"
  require (!(parsePassed 1 { op with nonce := 1 } expected response).isOk)
    "Simulation was rebound to another nonce"
  require (!(parsePassed 1 op [{ expected.head! with recipient := 3 }] response).isOk)
    "Simulation was rebound to another recipient"
  require (!(parsePassed 1 op expected (change
      (calls[0]!.setObjVal! "gasUsed" (toJson ("0xffffffffffff" : String))))).isOk)
    "Out-of-budget simulated gas was accepted"
  require (!(parsePassed 1 op expected (.arr (blocks.push blocks[0]!))).isOk)
    "Additional simulation blocks were accepted"
  IO.println "PASS: viem handleOps encoding, exact signed simulation events, and malformed-result rejection"
  return 0
