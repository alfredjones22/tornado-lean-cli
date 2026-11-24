import Lean
import Tornado.Cli.DepositBatch7702

/-! Only known public, unfunded note fixtures are read here. Exported fields
contain public deposit intents and actual checked planner output, no raw note. -/

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Cli

private def addr (raw : String) : Except String Nat := do
  let bytes ← parseHexBytes raw
  if bytes.size != 20 then throw "Expected a synthetic local sender address."
  return bytes.data.foldl (fun n byte => n * 256 + byte.toNat) 0

private def text (json : Json) (name : String) : Except String String :=
  (json.getObjVal? name).bind Json.getStr?

private def hex (bytes : ByteArray) : Json := .str ("0x" ++ bytesToHex bytes)
private def decimal (n : Nat) : Json := .str (toString n)

private def stepJson (step : DepositSend.Step) : Except String Json := do
  return Json.mkObj [
    ("kind", .str step.kind.text), ("to", .str (← Bundler.address step.to)),
    ("value", decimal step.value), ("data", hex step.data),
    ("pool", .str ("0x" ++ bytesToHex ((← Abi.addressWord step.pool).extract 12 32))),
    ("commitment", hex step.commitment), ("spender", decimal step.spender),
    ("approvalAmount", decimal step.approvalAmount)]

private def planJson (planned : DepositMulti.Plan) : Except String Json := do
  let batches ← planned.batches.mapM fun batch => return Json.arr (← batch.mapM stepJson)
  return Json.mkObj [
    ("mode", .str (match planned.mode with | .sequential => "sequential" | .simple7702 => "simple7702")),
    ("noteCount", toJson planned.noteCount), ("amount", decimal planned.amount),
    ("batches", .arr batches),
    ("firstBatchData", hex (← DepositBatch7702.callsData planned.batches[0]!))]

private def relabeledBackup (vectors : Json) : Except String String := do
  let groups ← (← vectors.getObjVal? "groups").getArr?
  let mut notes : Array Json := #[]
  for index in [0, 2] do
    notes := notes ++ (← (← groups[index]!.getObjVal? "notes").getArr?)
  let raw ← notes.mapM fun note => do
    let source ← text note "raw"
    let some preimage := (source.splitOn "-0x")[1]? | throw "Malformed known public note fixture."
    return "tornado-usdc-100-1-0x" ++ preimage
  return String.intercalate "\n" raw.toList

private def generate (caseName senderText raw : String) : Except String Json := do
  let sender ← addr senderText
  let items ← DepositMulti.publicItems raw .mainnet
  let total := items.foldl (fun sum item => sum + item.pool.amount) 0
  let mut pools : Array DepositMulti.PoolReading := #[]
  for item in items do
    let address ← addr item.pool.address
    if pools.any (fun row => row.address == address) then continue
    pools := pools.push ⟨address, item.pool.amount, if caseName == "eth-backup" then 0 else 1⟩
  let readings : DepositMulti.Readings := {
    chainId := 1, senderCode := ByteArray.empty, ethBalance := 10000000000000000000,
    tokenBalance := total, pools }
  let prepared ← DepositMulti.preparePlan items .mainnet sender readings
  let planned := prepared.output
  let publicItems ← items.mapM fun item => do
    return Json.mkObj [
      ("pool", .str item.pool.address), ("denomination", decimal item.pool.amount),
      ("commitment", hex item.commitment),
      ("token", match item.pool.asset.token with | none => .null | some token => .str token)]
  let sufficient := { readings with pools := pools.map (fun row => { row with allowance := total }) }
  let enough ← DepositMulti.plan items .mainnet sender sufficient
  let insufficientRejected := !(DepositMulti.plan items .mainnet sender
    { readings with tokenBalance := if total == 0 then 0 else total - 1 }).isOk
  let mut extra : List (String × Json) := []
  if caseName == "token-split" then
    let remaining := items.extract 4 items.size
    let first := items[0]!
    let laterReadings := { readings with
      tokenBalance := 2 * first.pool.amount
      senderCode := ByteArray.mk #[0xef, 0x01, 0]
      pools := pools.map (fun row => { row with allowance := 0 }) }
    let later ← DepositMulti.plan remaining .mainnet sender laterReadings true
    extra := [("replanned", ← planJson later)]
  return Json.mkObj ([
    ("case", .str caseName), ("sender", .str senderText),
    ("implementationHash", .str DepositBatch7702.implementationHash),
    ("scope", .str "actual checked DepositMulti.preparePlan and backup publicItems; synthetic ledger and local code placement"),
    ("items", .arr publicItems), ("plan", ← planJson planned),
    ("sufficientAllowancePlan", ← planJson enough),
    ("insufficientTokenRejected", .bool insufficientRejected)] ++ extra)

def main (args : List String) : IO UInt32 := do
  let result ← match args with
    | [caseName, sender] => do
      let raw ← if caseName == "eth-backup" then
          IO.FS.readFile "fixtures/seeded-backup-format.txt"
        else do
          let vectors ← IO.FS.readFile "fixtures/seeded-note-vectors.json"
          match Json.parse vectors >>= relabeledBackup with
          | .ok raw => pure raw
          | .error error => throw <| IO.userError error
      pure (generate caseName sender raw)
    | _ => pure (.error "Expected eth-backup or token-split and a synthetic sender.")
  match result with
  | .error error => IO.eprintln error; return 1
  | .ok fixture => IO.println fixture.compress; return 0
