import Tornado.Cli.WithdrawBatch

namespace Tornado.Cli.WithdrawBatch.Test

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Cli.WithdrawBatch Tornado.Cli.SmartAccountShow

private def require (label : String) (value : Bool) : IO Unit :=
  unless value do throw <| IO.userError s!"{label}: assertion failed"

private def checked (label : String) (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError s!"{label}: {message}"

private def expectFailure (label : String) (action : IO α) : IO Unit := do
  let failed ← try
      let _ ← action
      pure false
    catch _ => pure true
  require label failed

private def firstNote : String :=
  "tornado-eth-0.01-1-0x33567fb6463d588b0ef7ff2d415130e0d91059781005f504671ddc3f03c4adc8b873cfa627a16e46d1f33b81d9c7e86772a083575ccccb9104ed77057b53"

private def secondNote : String :=
  "tornado-eth-1-1-0x38ba0d601404fd62799e1f48f412425062db944406ad748338cdf17cc91e1b0e52370aca05d3731e2f6e278d0fb871ecedf5a9de9a20969a636b16acde90"

private def rawCalls : String :=
  "[{\"to\":\"0x00000000000000000000000000000000000000cc\",\"value\":\"5\",\"data\":\"0x12345678\"}," ++
  "{\"to\":\"0x00000000000000000000000000000000000000dd\",\"value\":\"0\",\"data\":\"0x\"}]"

private def safeCalls : String :=
  "{\"version\":\"1.0\",\"chainId\":\"1\",\"transactions\":" ++ rawCalls ++ "}"

private def replace (json : Json) (key : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert key value)
  | other => other

def main : IO Unit := do
  let selected ← checked "two selected notes" (parseBatchNotes
    (firstNote ++ "\n" ++ secondNote) .mainnet)
  let calls ← checked "raw calls" (parseContractCalls rawCalls .mainnet)
  let safe ← checked "Safe v1 calls" (parseContractCalls safeCalls .mainnet)
  require "Safe and raw calls have same ordered bytes" (safe == calls && calls.size == 2)
  let account : Account := ⟨0xaa, 0xbb, false, 0⟩
  let scope ← checked "call scope" (makeScope account none calls)
  let expectedHash :=
    "df42f7cb25a73ee1def16aacaab05947b21c508b66151f5e4ca671367ae7864f"
  require "viem ordered calls hash parity" (bytesToHex scope.callsHash == expectedHash)
  let firstTarget ← checked "first target" (checksumAddress 0xcc)
  let secondTarget ← checked "second target" (checksumAddress 0xdd)
  let owner ← checked "owner" (checksumAddress account.owner)
  let accountText ← checked "account" (checksumAddress account.address)
  let output ← checked "batch review" (render selected scope "/tmp/batch-status")
  let expected :=
    s!"Owner: {owner}\nSmart account: {accountText}\nNotes: 2\nTotal note value: 1.01 ETH\nReceiver: {accountText}\nContract calls: 2\n" ++
    s!"Ordered contract-calls hash: 0x{expectedHash}\n" ++
    s!"1. {firstTarget} · 5 wei · calldata 0x12345678 (4 bytes; 0x30ca65d5da355227c97ff836c9c6719af9d3835fc6bc72bddc50eeecc1bb2b25)\n" ++
    s!"2. {secondTarget} · 0 wei · calldata 0x (0 bytes; 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)\n" ++
    "Status directory: /tmp/batch-status\nDry run complete. No proof, fee quote, signature or UserOperation was created.\n"
  require "exact ordered call review" (output == expected)
  require "review does not expose notes" (!output.contains firstNote && !output.contains secondNote)
  let reversed ← checked "reversed scope" (makeScope account none #[calls[1]!, calls[0]!])
  require "call order changes binding hash" (reversed.callsHash != scope.callsHash)
  require "self-call blocked" (!(makeScope account none
    #[{ to := account.address, value := 0, data := ByteArray.empty }]).isOk)
  require "external receiver with calls blocked"
    (!(makeScope account (some 0xee) calls).isOk)
  let noCalls ← checked "plain scope" (makeScope account (some 0xee) #[])
  let plain ← checked "plain batch review" (render selected noCalls "/tmp/status")
  require "external receiver without calls" (plain.contains
    s!"Receiver: {← checked "receiver" (checksumAddress 0xee)}\nContract calls: 0")
  require "one note without calls rejected"
    (!(render [selected.head!] noCalls "/tmp/status").isOk)
  let oneWithCalls ← checked "one-note call scope" (makeScope account none #[calls[0]!])
  require "one note with calls accepted"
    ((render [selected.head!] oneWithCalls "/tmp/status").isOk)
  require "changed scope hash rejected" (!(render selected
    { scope with callsHash := ByteArray.empty } "/tmp/status").isOk)
  let parsed ← checked "raw JSON" (Json.parse rawCalls)
  let row := parsed.getArr?.toOption.get![0]!
  let delegate := Json.arr #[replace row "operation" (toJson (1 : Nat))]
  require "delegatecall rejected" (!(parseContractCalls delegate.compress .mainnet).isOk)
  let method := Json.arr #[replace row "contractMethod" (Json.mkObj
    [("name", toJson ("transfer" : String))])]
  require "unverified Safe method rejected" (!(parseContractCalls method.compress .mainnet).isOk)
  let oversized := Json.arr #[replace row "data" (toJson
    ("0x" ++ String.ofList (List.replicate (16385 * 2) '0')))]
  require "oversized calldata rejected" (!(parseContractCalls oversized.compress .mainnet).isOk)
  require "wrong Safe chain rejected" (!(parseContractCalls
    (replace (← checked "Safe JSON" (Json.parse safeCalls)) "chainId" (toJson ("11155111" : String))).compress
    .mainnet).isOk)
  let help ← withdrawBatchCommand ["--help"]
  require "runnable help" (help.startsWith "Usage: tornado withdraw batch")
  expectFailure "no-flag send fails closed" (withdrawBatchCommand [])
  expectFailure "missing protected inputs rejected" (withdrawBatchCommand ["--dry-run"])
  let callsMade ← IO.mkRef ([] : List JsonRpc.Method)
  let wrongChain : JsonRpc.Method → Array Json → IO Json := fun method _ => do
    callsMade.modify (· ++ [method])
    if method == .chainId then pure (toJson ("0xaa36a7" : String))
    else throw <| IO.userError "Unexpected RPC request after wrong chain."
  expectFailure "wrong chain account lookup" (loadAccountWith .mainnet account.owner wrongChain)
  require "wrong chain stops before code reads" ((← callsMade.get) == [.chainId])
  IO.println "PASS: protected batch review, Safe/raw ordered call hash parity, scope guards, and fail-closed account checks"

end Tornado.Cli.WithdrawBatch.Test

def main : IO Unit := Tornado.Cli.WithdrawBatch.Test.main
