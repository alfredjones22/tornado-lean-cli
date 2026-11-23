import Tornado.Cli.ProverWorker
import Tornado.Runtime.ProverWorkerClient

/-! Public, unfunded note fixtures only. Signatures bind public synthetic
digests; no proof, funded operation or network transaction is generated. -/

open Lean Tornado.Domain Tornado.Crypto Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error _ => throw <| IO.userError "Invalid public metadata fixture."

private def rejects (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ => return true

private def number (raw : String) : IO Nat := do
  let bytes ← checked <| parseHexBytes raw
  return bytes.data.foldl (fun n b => n * 256 + b.toNat) 0

private def rejectWire (raw : String) : IO Unit := do
  match Metadata.decode raw with
  | .ok _ => throw <| IO.userError "Malformed public metadata wire was accepted."
  | .error message => do
    require (message == "Invalid prover worker metadata")
      "Metadata parser reflected input or exposed another diagnostic."

def main (args : List String) : IO UInt32 := do
  let [workerPath, privateDir] := args
    | throw <| IO.userError "Usage: prover_worker_metadata_test <worker> <private-test-dir>"
  require ((System.FilePath.mk workerPath).isAbsolute &&
    (System.FilePath.mk privateDir).isAbsolute) "Metadata fixture paths must be absolute."
  ProtectedIO.checkPrivateDirectory privateDir
  let raw := "tornado-eth-0.01-1-0x" ++ String.ofList (List.replicate 124 '1')
  let secondRaw := "tornado-eth-0.01-1-0x" ++ String.ofList (List.replicate 124 '2')
  let selected ← checked <| Tornado.Cli.History.selectNote raw .mainnet none
  let expected : Metadata := {
    chainId := 1
    pool := ← number selected.note.pool.address
    commitment := ← number selected.publicIdentity.commitment
    nullifierHash := ← number selected.publicIdentity.nullifierHash
    amount := selected.note.pool.amount
    denomination := selected.note.pool.denomination
    asset := selected.note.pool.asset.symbol
    statusFileName := ← checked <| Tornado.Cli.WithdrawOne.statusFileName selected.note }
  let _ ← checked expected.validate
  let encoded := expected.encode
  require ((← checked <| Metadata.decode encoded) == expected && encoded.utf8ByteSize <= 1536)
    "Canonical public metadata failed its bounded roundtrip."
  rejectWire (expected.toJson.setObjVal! "note" (toJson raw)).compress
  rejectWire (expected.toJson.setObjVal! "nullifier" (toJson ("private" : String))).compress
  rejectWire (encoded ++ "\n")
  rejectWire (encoded.replace "\"chainId\":\"1\"" "\"chainId\":\"01\"")
  rejectWire (encoded.replace "\"version\":1" "\"version\":1,\"version\":1")
  rejectWire (Metadata.encode { expected with amount := expected.amount + 1 })
  rejectWire (Metadata.encode { expected with pool := 1 })
  rejectWire (Metadata.encode { expected with statusFileName := "../" ++ expected.statusFileName })
  rejectWire (Metadata.encode { expected with denomination := "1" })
  rejectWire (String.ofList (List.replicate 1537 'x'))
  let request : Request := {
    chainId := expected.chainId, pool := expected.pool,
    commitment := expected.commitment, nullifierHash := expected.nullifierHash,
    leafIndex := 0, root := 0, siblings := Array.replicate 20 0,
    pathIndices := Array.replicate 20 0, recipient := 1, relayer := 0, fee := 0, refund := 0 }
  require (expected.matchesRequest request &&
    !expected.matchesRequest { request with commitment := request.commitment + 1 })
    "Metadata failed to bind selected public note identity."
  let notePath := privateDir ++ "/public-note"
  ProtectedIO.createPrivate notePath raw.toUTF8
  let inspected ← ProverWorkerClient.inspectPrototype workerPath notePath 1
  require (inspected == expected) "Worker metadata differs from the public unfunded fixture."
  let fixture ← checked <| Json.parse (← IO.FS.readFile "fixtures/prover-signer-public.json")
  let fixtureText (name : String) : IO String := do
    checked <| (← checked <| fixture.getObjVal? name).getStr?
  let fixtureBytes (name : String) : IO ByteArray := do
    checked <| parseHexBytes (← fixtureText name)
  require (raw == (← fixtureText "note")) "Synthetic signer fixture note changed."
  let identity ← ProverWorkerClient.inspectSignerPrototype workerPath notePath inspected
  require (identity.sender == (← number (← fixtureText "sender")) &&
    identity.publicKey == (← fixtureBytes "publicKey"))
    "Worker note-derived public identity differs from offline viem."
  let signRequest : ProverSignerWire.SignRequest := {
    metadata := inspected, expectedSender := identity.sender
    operationHash := ← fixtureBytes "operationHash" }
  require ((← checked <| signRequest.authorizationHash) == (← fixtureBytes "authorizationHash"))
    "Worker authorization preimage differs from viem's selected-chain/delegate/nonce0."
  require ((← checked <| ProverSignerWire.SignRequest.decode signRequest.encode) == signRequest)
    "Canonical isolated signer request failed roundtrip."
  require (!(ProverSignerWire.SignRequest.decode
    (signRequest.toJson.setObjVal! "nullifier" (toJson ("SECRET" : String))).compress).isOk &&
    !(ProverSignerWire.SignRequest.decode (signRequest.encode ++ "\n")).isOk &&
    !(ProverSignerWire.SignRequest.decode
      (signRequest.toJson.setObjVal! "delegate" (toJson ("1" : String))).compress).isOk &&
    !(ProverSignerWire.SignRequest.decode (String.ofList (List.replicate 3073 'x'))).isOk)
    "Isolated signer request accepted extra secret/delegate fields or unbounded framing."
  let signed ← ProverWorkerClient.signPrototype workerPath notePath none signRequest
  require (signed.identity == identity &&
    signed.operationSignature == (← fixtureBytes "operationSignature") &&
    signed.authorizationSignature == (← fixtureBytes "authorizationSignature"))
    "Isolated worker signatures differ from offline viem."
  let auth ← checked <| ProverWorkerClient.authorizationOf signRequest signed
  require (auth.chainId == 1 && auth.delegate == ProverSignerWire.delegate && auth.nonce == 0 &&
    auth.yParity == 1) "Worker authorization transport scope changed."
  let altered := signed.operationSignature.set! 0 (signed.operationSignature[0]! ^^^ 1)
  require (← rejects <| ProverWorkerClient.acceptSignResponse signRequest
    { signed with operationSignature := altered })
    "Parent accepted a corrupted public operation signature."
  let wrongRecovery := signed.authorizationSignature.set! 64 27
  require (← rejects <| ProverWorkerClient.acceptSignResponse signRequest
    { signed with authorizationSignature := wrongRecovery })
    "Parent accepted a substituted authorization recovery ID."
  require (← rejects <| ProverWorkerClient.signPrototype workerPath notePath none
    { signRequest with expectedSender := identity.sender + 1 })
    "Worker signed for a substituted expected sender."
  require (← rejects <| ProverWorkerClient.signPrototype workerPath notePath none
    { signRequest with metadata := { inspected with commitment := inspected.commitment + 1 } })
    "Worker signed for another public note identity."
  let batchPath := privateDir ++ "/public-note-batch"
  ProtectedIO.createPrivate batchPath (raw ++ "\n" ++ secondRaw).toUTF8
  let batch ← ProverWorkerClient.inspectBatchPrototype workerPath batchPath 1
  require (batch.size == 2 && batch[0]! == inspected &&
    batch[1]!.commitment != inspected.commitment)
    "Ordered batch inspection changed note order or omitted a note."
  require ((← checked <| BatchMetadata.decode (BatchMetadata.encode batch)) == batch &&
    !(BatchMetadata.decode (BatchMetadata.encode #[inspected, inspected])).isOk &&
    !(BatchMetadata.decode (BatchMetadata.encode (Array.replicate 13 inspected))).isOk &&
    !(BatchMetadata.decode ((BatchMetadata.toJson batch).setObjVal!
      "preimage" (toJson ("SECRET" : String))).compress).isOk)
    "Public batch wire accepted duplicates, extra secret fields or excess notes."
  let singleton ← ProverWorkerClient.inspectBatchPrototype workerPath notePath 1
  require (singleton == #[inspected]) "Single-note plus calls batch inspection failed."
  let malformedPath := privateDir ++ "/malformed-trailing-note"
  ProtectedIO.createPrivate malformedPath (raw ++ "\ntornado-eth-malformed").toUTF8
  require (← rejects <| ProverWorkerClient.inspectBatchPrototype workerPath malformedPath 1)
    "Worker silently omitted a malformed trailing note."
  let duplicatePath := privateDir ++ "/duplicated-note"
  ProtectedIO.createPrivate duplicatePath (raw ++ "\n" ++ raw).toUTF8
  require (← rejects <| ProverWorkerClient.inspectBatchPrototype workerPath duplicatePath 1)
    "Worker accepted a repeated nullifier in batch selection."
  require (← rejects <| ProverWorkerClient.inspectPrototype workerPath batchPath 1)
    "Multi-note metadata inspection silently chose a note."
  let second ← ProverWorkerClient.inspectPrototype workerPath batchPath 1 (some "2")
  let secondSelected ← checked <| Tornado.Cli.History.selectNote secondRaw .mainnet none
  require (second.commitment == (← number secondSelected.publicIdentity.commitment) &&
    second.statusFileName == (← checked <| Tornado.Cli.WithdrawOne.statusFileName secondSelected.note))
    "Selected metadata index or keyed status label changed."
  require (← rejects <| ProverWorkerClient.inspectPrototype workerPath notePath 11155111)
    "Metadata inspection accepted a note on another chain."
  require (← rejects <| ProverWorkerClient.inspectPrototype workerPath notePath 2)
    "Metadata inspection accepted an unsupported chain."
  require (← rejects <| ProverWorkerClient.inspectPrototype workerPath notePath 1 (some "0"))
    "Metadata inspection accepted index zero."
  require (← rejects <| ProverWorkerClient.inspectPrototype "relative-worker" notePath 1)
    "Metadata inspection accepted a relative worker path."
  let failed ← IO.Process.output {
    cmd := workerPath
    args := #["--inspect", "--chain", "1", "--note-file", notePath ++ ".missing"]
    inheritEnv := false }
  require (failed.exitCode != 0 && failed.stdout == "" && failed.stderr == "Prover worker failed.\n")
    "Metadata worker failure disclosed input or used an unexpected diagnostic."
  IO.println "PASS: isolated public metadata and viem-parity ephemeral signatures, strict wire, recovery verification, and sanitized failures"
  return 0
