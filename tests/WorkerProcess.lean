import Tornado.Runtime.ProverWorkerClient

/-! Public-only process regression: an exited worker can have a live child
holding its stdout pipe. Exit observation and output completion are separate.
No real note, key, proof, signature, RPC, or transaction is used. -/

open Tornado.Protocol.ProverWorkerWire Tornado.Runtime

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def publicMetadata : Metadata := {
  chainId := 1
  pool := 0x199112eb461ea7eec1d75b33343542e1d069b41c
  commitment := 1
  nullifierHash := 2
  amount := 10000000000000000
  denomination := "0.01"
  asset := "ETH"
  statusFileName := "tornado-withdraw-1-" ++ String.ofList (List.replicate 64 '1') ++ ".json" }

private def writeWorker (path : System.FilePath) (output : String)
    (holdStdout : Bool := true) (exitCode : Nat := 0) : IO Unit := do
  -- These records contain only fixed numeric/catalogue fixture fields.
  require (!output.toList.contains '\'') "Unexpected shell quote in public process fixture."
  let delay := if holdStdout then "/bin/sleep 0.6 &\n" else ""
  IO.FS.writeFile path
    ("#!/bin/sh\n" ++ delay ++ "printf '%s\\n' '" ++ output ++ "'\nexit " ++ toString exitCode ++ "\n")
  IO.setAccessRights path { user := { read := true, write := true, execution := true } }

private def rejects (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

def main : IO Unit := IO.FS.withTempDir fun directory => do
  let note := directory / "public-note-placeholder"
  let worker := directory / "public-worker"
  IO.FS.writeFile note "Synthetic public path fixture; fake worker never reads it.\n"
  IO.setAccessRights note { user := { read := true, write := true } }
  let canonical := match Metadata.decode publicMetadata.encode with
    | .ok metadata => metadata == publicMetadata
    | .error _ => false
  require canonical
    "Public metadata process fixture is not canonical."
  writeWorker worker publicMetadata.encode
  for _ in [0:3] do
    let started ← IO.monoMsNow
    let result ← ProverWorkerClient.inspectPrototype worker.toString note.toString 1 none 5000
    require (result == publicMetadata && (← IO.monoMsNow) - started >= 400)
      "Metadata worker exit was confused with stdout completion or returned wrong public data."
  let secondLabel := "tornado-withdraw-1-" ++ String.ofList (List.replicate 64 '2') ++ ".json"
  let second := { publicMetadata with commitment := 3, nullifierHash := 4, statusFileName := secondLabel }
  let batch := #[publicMetadata, second]
  writeWorker worker (BatchMetadata.encode batch)
  let batchResult ← ProverWorkerClient.inspectBatchPrototype worker.toString note.toString 1 5000
  require (batchResult == batch) "Batch inspection failed after worker exit before pipe EOF."
  writeWorker worker "invalid public metadata"
  require (← rejects <| ProverWorkerClient.inspectPrototype worker.toString note.toString 1 none 5000)
    "An exited worker's malformed metadata was accepted."
  writeWorker worker publicMetadata.encode
  require (← rejects <| ProverWorkerClient.inspectPrototype worker.toString note.toString 1 none 150)
    "Exited worker with a held-open pipe bypassed the output timeout."
  writeWorker worker publicMetadata.encode false 9
  require (← rejects <| ProverWorkerClient.inspectPrototype worker.toString note.toString 1 none 5000)
    "A failing worker's canonical-looking stdout was accepted."
  IO.println "PASS: worker exit before stdout EOF, repeated single/batch inspection, timeout, malformed-output and nonzero-exit rejection"
