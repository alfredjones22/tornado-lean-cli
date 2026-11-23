import Tornado.Cli.ProverWorker
import Tornado.Spec.WorkerDisclosure

/-! Public unfunded fixtures and injected local effects only. No network,
funded proof, private wallet key, or transaction submission is exercised. -/

open Lean Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire Tornado.Runtime.WorkerProgram

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error _ => throw <| IO.userError "Invalid public worker-disclosure fixture."

private def value (result : Execution mode α) : IO α :=
  match result.value with
  | some value => pure value
  | none => throw <| IO.userError "Restricted worker unexpectedly failed."

private def backend (events : IO.Ref (List Effect)) (note request : ByteArray) : Backend := {
  protect := events.modify (· ++ [.protect])
  readNote := do events.modify (· ++ [.read .note]); return note
  readRequest := do events.modify (· ++ [.read .request]); return request
  readAsset := fun kind => do
    events.modify (· ++ [.read (.asset kind)])
    return "invalid public asset fixture".toUTF8
  entropy32 := do
    events.modify (· ++ [.entropy32])
    throw <| IO.userError "Unexpected entropy draw in public metadata/signing test." }

private def terminalChecks (output : Terminal mode) (expected : String) : IO Unit := do
  require (output.stdout == expected ++ "\n" && output.stderr == "" && output.exitCode == 0)
    "Canonical typed response or terminal framing changed."
  require ((output.stdout.splitOn "\n").length == 2)
    "An extra stdout line escaped the typed terminal gate."

private def failureChecks (output : Terminal mode) : IO Unit :=
  require (output.stdout == "" && output.stderr == "Prover worker failed.\n" &&
    output.exitCode == 1) "Failure reflected input or added another output channel."

def main : IO Unit := do
  let fixture ← checked <| Json.parse (← IO.FS.readFile "fixtures/prover-signer-public.json")
  let field (key : String) : IO String := do
    checked <| (← checked <| fixture.getObjVal? key).getStr?
  let bytes (key : String) : IO ByteArray := do checked <| parseHexBytes (← field key)
  let note ← field "note"
  let events ← IO.mkRef ([] : List Effect)
  let hardware := backend events note.toUTF8 ByteArray.empty
  let metadataResult ← evaluateWith hardware (Tornado.Cli.ProverWorker.metadataProgram 1 none)
  let metadata ← value metadataResult
  let exactMetadata := [.protect, .read .note]
  require (metadataResult.effects == exactMetadata && (← events.get) == exactMetadata)
    "Metadata used an unlisted effect or read before protection."
  terminalChecks (terminal (some (.metadata metadata))) metadata.encode
  require (!(metadata.encode.splitOn note).length > 1)
    "Raw note appeared in trusted-parent metadata."
  failureChecks (terminal (some (.metadata { metadata with asset := "SECRET-MARKER" })))
  let scope : Scope := {
    noteFile := "/selected/protected-note", requestFile := some "/selected/public-request",
    assetsRoot := some "/selected/assets" }
  require (scope.path .note == some "/selected/protected-note" &&
    scope.path .request == some "/selected/public-request" &&
    scope.path (.asset .graph) == some "/selected/assets/fixtures/witness-vm-selected-components.json")
    "Fixed configured path slots changed."
  events.set []
  let identityResult ← evaluateWith hardware (Tornado.Cli.ProverWorker.identityProgram 1 none)
  let identity ← value identityResult
  require (identity.publicKey == (← bytes "publicKey") &&
    identityResult.effects == exactMetadata && (← events.get) == exactMetadata)
    "Note-derived identity changed or used an unlisted effect."
  terminalChecks (terminal (some (.identity identity))) identity.encode
  let request : ProverSignerWire.SignRequest := {
    metadata, expectedSender := identity.sender, operationHash := ← bytes "operationHash" }
  let signing : Program .sign (Response .sign) := do
    let input ← Tornado.Cli.ProverWorker.signRequestProgram
    return .signed input (← Tornado.Cli.ProverWorker.signedProgram none input)
  events.set []
  let signedResult ← evaluateWith (backend events note.toUTF8 request.encode.toUTF8) signing
  let signedResponse ← value signedResult
  let .signed accepted signed := signedResponse
  require (accepted == request && signed.operationSignature == (← bytes "operationSignature") &&
    signed.authorizationSignature == (← bytes "authorizationSignature"))
    "Restricted signer changed the request or pinned viem signatures."
  let exactSigning := [.protect, .read .request, .read .note]
  require (signedResult.effects == exactSigning && (← events.get) == exactSigning)
    "Signer used entropy/assets, extra reads or an unrecorded effect."
  terminalChecks (terminal (some signedResponse)) signed.encode
  failureChecks (terminal (some (.signed request { signed with requestHash := ByteArray.empty })))
  let second := "tornado-eth-0.01-1-0x" ++ String.ofList (List.replicate 124 '2')
  events.set []
  let batchResult ← evaluateWith (backend events (note ++ "\n" ++ second).toUTF8 ByteArray.empty)
    (Tornado.Cli.ProverWorker.batchProgram 1)
  let items ← value batchResult
  require (items.size == 2 && batchResult.effects == exactMetadata &&
    (← events.get) == exactMetadata) "Batch metadata used extra reads or lost a selected note."
  terminalChecks (terminal (some (.batch items))) (BatchMetadata.encode items)
  -- Secret-bearing parser/IO diagnostics are never accepted output values.
  events.set []
  let malicious := backend events "SECRET-MARKER malformed note".toUTF8 ByteArray.empty
  let rejected ← evaluateWith malicious (Tornado.Cli.ProverWorker.metadataProgram 1 none)
  require rejected.value.isNone "Malformed note unexpectedly produced metadata."
  failureChecks (terminal (rejected.value.map Response.metadata))
  events.set []
  let readFailure : Backend := { hardware with readNote := do
    events.modify (· ++ [.read .note]); throw <| IO.userError "SECRET-MARKER raw exception" }
  let failed ← evaluateWith readFailure (Tornado.Cli.ProverWorker.metadataProgram 1 none)
  require (failed.effects == exactMetadata && (← events.get) == exactMetadata)
    "Failed read was omitted from the capability trace."
  failureChecks (terminal (failed.value.map Response.metadata))
  events.set []
  let protectionFailure : Backend := { hardware with protect := do
    events.modify (· ++ [.protect]); throw <| IO.userError "SECRET-MARKER protection error" }
  let protectionResult ← evaluateWith protectionFailure (Tornado.Cli.ProverWorker.metadataProgram 1 none)
  require (protectionResult.value.isNone && protectionResult.effects == [.protect] &&
    (← events.get) == [.protect]) "A read followed failed core-dump suppression."
  failureChecks (terminal (protectionResult.value.map Response.metadata))
  -- The actual proof program has no hidden full-prover IO callback: its
  -- request and three fixed asset reads are independently observable.
  let proofRequest : Request := {
    chainId := 1, pool := metadata.pool, commitment := metadata.commitment,
    nullifierHash := metadata.nullifierHash, leafIndex := 0, root := 0,
    siblings := Array.replicate 20 0, pathIndices := Array.replicate 20 0,
    recipient := 1, relayer := 0, fee := 0, refund := 0 }
  let proving : Program .prove (Response .prove) := do
    let input ← Tornado.Cli.ProverWorker.publicRequestProgram
    return .proof input (← Tornado.Cli.ProverWorker.proofProgram none input)
  events.set []
  let proofResult ← evaluateWith (backend events note.toUTF8 proofRequest.encode.toUTF8) proving
  let exactAssets := [.protect, .read .request, .read (.asset .circuit),
    .read (.asset .key), .read (.asset .graph)]
  require (proofResult.value.isNone && proofResult.effects == exactAssets &&
    (← events.get) == exactAssets) "Unauthenticated assets reached secret note/entropy/proof work."
  failureChecks (terminal proofResult.value)
  failureChecks (terminal (some (.proof proofRequest {
    requestHash := proofRequest.hash, proof := ByteArray.empty,
    signals := proofRequest.publicSignals })))
  -- Shared pure sampler control is instantiated in the same effect monad.
  -- First zero is rejected; then r=1,s=2 are drawn separately without prefetch.
  let draws ← IO.mkRef (0 : Nat)
  events.set []
  let entropy : Backend := { hardware with entropy32 := do
    events.modify (· ++ [.entropy32])
    let index ← draws.get
    draws.set (index + 1)
    return (ByteArray.mk (Array.replicate 31 0)).push index.toUInt8 }
  let sampling : Program .prove (ProofBlinding.Scalar × ProofBlinding.Scalar) :=
    ProofBlinding.samplePairLoop
      (do WorkerProgram.liftExcept <| ProofBlinding.admitCandidate (← WorkerProgram.entropy32 rfl))
      .fail ProofBlinding.maxAttempts
  let sampled ← evaluateWith entropy sampling
  let (r, s) ← value sampled
  require (r.value == 1 && s.value == 2 && (← draws.get) == 3 &&
    sampled.effects == [.protect, .entropy32, .entropy32, .entropy32] &&
    (← events.get) == sampled.effects) "Sampler hid, reused or prefetched an entropy draw."
  for wrongLength in [false, true] do
    events.set []
    let entropyFailure : Backend := { hardware with entropy32 := do
      events.modify (· ++ [.entropy32])
      if wrongLength then return ByteArray.mk (Array.replicate 31 0)
      throw <| IO.userError "SECRET-MARKER entropy backend exception" }
    let rejected ← evaluateWith entropyFailure sampling
    require (rejected.value.isNone && rejected.effects == [.protect, .entropy32] &&
      (← events.get) == rejected.effects)
      "Malformed or failed entropy draw did not terminate immediately."
    failureChecks (terminal (none : Option (Response .prove)))
  events.set []
  let exhaustedEntropy : Backend := { hardware with entropy32 := do
    events.modify (· ++ [.entropy32]); return ByteArray.mk (Array.replicate 32 0) }
  let exhausted ← evaluateWith exhaustedEntropy sampling
  require (exhausted.value.isNone && exhausted.effects ==
    .protect :: List.replicate ProofBlinding.maxAttempts .entropy32 &&
    (← events.get) == exhausted.effects)
    "Rejected entropy did not stop at the shared exact draw budget."
  -- Native bounded-reader errors pass through the same fixed failure path.
  -- This public graph is larger than the request slot's4096-byte limit.
  let root ← IO.currentDir
  let largeRequest := (root / "fixtures/witness-vm-selected-components.json").toString
  let boundedRequest ← evaluateWith (nativeBackend {
    noteFile := "/unused", requestFile := some largeRequest })
    Tornado.Cli.ProverWorker.publicRequestProgram
  require (boundedRequest.value.isNone &&
    boundedRequest.effects == [.protect, .read .request])
    "Native request-size rejection was not sanitized and traced."
  failureChecks (terminal (boundedRequest.value.map (fun input => Response.proof input {
    requestHash := input.hash, proof := ByteArray.empty, signals := input.publicSignals })))
  let missingAsset ← evaluateWith (nativeBackend {
    noteFile := "/unused", assetsRoot := some (root / ".worker-missing-public-assets").toString })
    (WorkerProgram.read (.asset .circuit) rfl : Program .prove ByteArray)
  require (missingAsset.value.isNone &&
    missingAsset.effects == [.protect, .read (.asset .circuit)])
    "Native asset-open error was not sanitized and traced."
  for slot in [File.request, File.asset .circuit] do
    events.set []
    let fault : Backend := { hardware with
      readRequest := do
        events.modify (· ++ [.read .request]); throw <| IO.userError "SECRET-MARKER request error"
      readAsset := fun kind => do
        events.modify (· ++ [.read (.asset kind)]); throw <| IO.userError "SECRET-MARKER asset error" }
    let rejected ← evaluateWith fault
      (WorkerProgram.read slot (by cases slot <;> simp_all [MayRead]) : Program .prove ByteArray)
    require (rejected.value.isNone && rejected.effects == [.protect, .read slot] &&
      (← events.get) == rejected.effects) "Public-file exception escaped fixed-error handling."
  IO.println "PASS: restricted worker capabilities, typed canonical output, fixed failures, and explicit entropy effects"
