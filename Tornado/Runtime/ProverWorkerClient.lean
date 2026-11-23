import Tornado.Protocol.ProverWorkerWire
import Tornado.Protocol.ProverSignerWire
import Tornado.Runtime.NativeSigner
import Tornado.Runtime.Bundler
import Tornado.Protocol.ClassicVerifyingKey
import Tornado.Protocol.Abi

/-!
Public-data acceptance boundary for the experimental separate Classic prover
worker. This module never opens a note file. Its caller must have already
reviewed the selected pool, same-block history, spent status, recipient and
fee before constructing `Request`. The worker is experimental; opting into
live use does not make the variable-time Lean witness/prover constant-time
or zeroize its secret values.

The parent deliberately treats the worker as untrusted: it rejects excessive
or noncanonical output, binds a response to the exact request, decodes all
eight proof words with canonical on-curve checks, verifies the proof against
the compiled Classic key, and only then constructs public pool calldata.
-/

namespace Tornado.Runtime.ProverWorkerClient

open Tornado.Protocol
open Tornado.Protocol.ProverWorkerWire

/-- Decode the eight 32-byte big-endian Solidity words without field
    reduction. The Fp2 limbs are in Solidity order `c1,c0` and therefore
    swapped when passed to the native G2 checker. -/
def decodeProof (bytes : ByteArray) : Except String BN254Groth16Verify.Proof := do
  if bytes.size != 256 then
    throw "Classic Solidity proof must be exactly 256 bytes."
  let mut words : Array Nat := #[]
  for i in [0:8] do
    let mut value := 0
    for j in [0:32] do
      value := value * 256 + bytes[i * 32 + j]!.toNat
    words := words.push value
  let a ← BN254G1.Affine.checked words[0]! words[1]!
  let b ← BN254G2.Affine.checked words[3]! words[2]! words[5]! words[4]!
  let c ← BN254G1.Affine.checked words[6]! words[7]!
  return { a, b, c }

/-- A public proof whose constructor is only available after all checks. The
    proof points and six public signals remain public. -/
structure Accepted (request : Request) where
  private mk ::
  proofBytes : ByteArray
  signals : Array Nat
  calldata : ByteArray
  proof : BN254Groth16Verify.Proof
  responseHash : ByteArray
  rootWord : ByteArray
  nullifierWord : ByteArray
  hashBound : responseHash = request.hash
  signalsBound : signals = request.publicSignals
  decoded : decodeProof proofBytes = .ok proof
  verified : ClassicVerifyingKey.verifyClassic proof signals = .ok true
  rootEncoded : Abi.uintWord request.root = .ok rootWord
  nullifierEncoded : Abi.uintWord request.nullifierHash = .ok nullifierWord
  calldataBound : Abi.poolWithdraw proofBytes rootWord nullifierWord
    request.recipient request.relayer request.fee request.refund = .ok calldata

/-- Reject a worker response unless the exact reviewed public request hash
    and six signals match and the proof verifies under the compiled key. The
    response cannot change the pool, chain, recipient, fee or root. -/
def acceptResponse (request : Request) (result : Result) :
    Except String (Accepted request) := do
  request.validate
  if hHash : result.requestHash = request.hash then
    if hSignals : result.signals = request.publicSignals then
      match hProof : decodeProof result.proof with
      | .error message => throw message
      | .ok proof =>
        match hVerified : ClassicVerifyingKey.verifyClassic proof result.signals with
        | .error message => throw message
        | .ok false => throw "Classic proof equation rejected the worker response."
        | .ok true =>
          match hRoot : Abi.uintWord request.root with
          | .error message => throw message
          | .ok rootWord =>
            match hNullifier : Abi.uintWord request.nullifierHash with
            | .error message => throw message
            | .ok nullifierWord =>
              match hCall : Abi.poolWithdraw result.proof rootWord nullifierWord
                  request.recipient request.relayer request.fee request.refund with
              | .error message => throw message
              | .ok calldata =>
                return ⟨result.proof, result.signals, calldata, proof,
                  result.requestHash, rootWord, nullifierWord, hHash,
                  hSignals, hProof, hVerified,
                  hRoot, hNullifier, hCall⟩
    else throw "Prover public signals differ from the reviewed withdrawal."
  else throw "Prover response does not match the public request."

/-- An accepted response is bound to the exact canonical reviewed request and
    to the six signals accepted by the compiled-key Classic verifier. -/
theorem accepted_binds_review_and_verifies (request : Request)
    (accepted : Accepted request) :
    accepted.responseHash = request.hash ∧
    accepted.signals = request.publicSignals ∧
    ClassicVerifyingKey.verifyClassic accepted.proof accepted.signals = .ok true :=
  ⟨accepted.hashBound, accepted.signalsBound, accepted.verified⟩

/- The process launcher is below the pure acceptance gate. It passes only
   public JSON and absolute paths to a direct child; no shell is involved. -/

def maxResponseBytes : Nat := 4096
def workerTimeoutMs : Nat := 15 * 60 * 1000

private def readCapped (handle : IO.FS.Handle) (limit : Nat := maxResponseBytes) : IO ByteArray := do
  let mut output := ByteArray.empty
  for _ in [0:limit + 1] do
    let remaining := limit + 1 - output.size
    let chunk ← handle.read (min remaining 1024).toUSize
    if chunk.isEmpty then return output
    if output.size + chunk.size > limit then
      throw <| IO.userError "Prover worker output exceeded the public-data limit."
    output := output ++ chunk
  throw <| IO.userError "Prover worker output exceeded the public-data limit."

private def childOutput (child : IO.Process.Child
    { stdin := .null, stdout := .piped, stderr := .null })
    (timeoutMs : Nat) (limit : Nat := maxResponseBytes) : IO ByteArray := do
  let reader ← IO.asTask (readCapped child.stdout limit)
  let started ← IO.monoMsNow
  repeat
    let status ← child.tryWait
    if status.isSome && status != some 0 then
      throw <| IO.userError "Prover worker failed."
    if ← IO.hasFinished reader then
      let output ← match ← IO.wait reader with
        | .ok bytes => pure bytes
        | .error _ => throw <| IO.userError "Prover worker output read failed."
      match status with
      | some 0 => return output
      | some _ => throw <| IO.userError "Prover worker failed."
      | none => pure ()
    if (← IO.monoMsNow) - started >= timeoutMs then
      throw <| IO.userError "Prover worker exceeded the time limit."
    IO.sleep 100
  throw <| IO.userError "Prover worker stopped without a result."

/-- Best-effort bounded reaping after a failed or timed-out worker run.
    Lean's portable child API exposes SIGTERM, but not SIGKILL; a hostile child
    that ignores termination can outlive this best-effort cleanup. -/
private def terminateChild (child : IO.Process.Child
    { stdin := .null, stdout := .piped, stderr := .null }) : IO Unit := do
  try child.kill catch _ => pure ()
  for _ in [0:20] do
    let status ← try child.tryWait catch _ => pure none
    if status.isSome then
      try
        let _ ← child.wait
        pure ()
      catch _ => pure ()
      return
    IO.sleep 100

/-- Obtain a selected note's public metadata without opening its protected
backup in the parent. The worker executable remains a trusted, unpinned
experimental boundary. The returned commitment/nullifier association must not be
logged, persisted or forwarded to an unrelated endpoint. -/
def inspectPrototype (workerPath noteFile : String) (chainId : Nat)
    (noteIndex : Option String := none)
    (timeoutMs : Nat := workerTimeoutMs) : IO Metadata := do
  if !(System.FilePath.mk workerPath).isAbsolute ||
      !(System.FilePath.mk noteFile).isAbsolute ||
      (chainId != 1 && chainId != 11155111) ||
      timeoutMs == 0 || timeoutMs > workerTimeoutMs then
    throw <| IO.userError "Invalid prover metadata inspection request."
  let args := #["--inspect", "--note-file", noteFile, "--chain", toString chainId] ++
    match noteIndex with
    | none => #[]
    | some index => #["--note-index", index]
  let child ← try
    IO.Process.spawn {
      cmd := workerPath, args := args,
      stdin := .null, stdout := .piped, stderr := .null,
      inheritEnv := false, setsid := true }
    catch _ => throw <| IO.userError "Prover metadata worker could not start."
  try
    let output ← childOutput child timeoutMs
    if output.isEmpty || output[output.size - 1]! != 10 then
      throw <| IO.userError "Invalid prover metadata framing."
    let some raw := String.fromUTF8? (output.extract 0 (output.size - 1))
      | throw <| IO.userError "Invalid prover metadata encoding."
    let metadata ← match Metadata.decode raw with
      | .ok metadata => pure metadata
      | .error _ => throw <| IO.userError "Invalid prover worker metadata."
    if metadata.chainId != chainId then
      throw <| IO.userError "Prover metadata belongs to another network."
    return metadata
  catch _ =>
    terminateChild child
    throw <| IO.userError "Prover metadata inspection failed or was rejected."

/-- Launch the isolated worker with a public request file and a protected
    note-file path. This function does not read or parse the note file. The
    child must emit exactly one canonical Result JSON line and terminate within
    the bounded time/output limits. A failure leaks no worker stderr. -/
def runPrototype (workerPath assetsRoot noteFile : String)
    (noteIndex : Option String) (request : Request)
    (timeoutMs : Nat := workerTimeoutMs) : IO (Accepted request) := do
  let checkAbsolute (path : String) : IO Unit :=
    unless (System.FilePath.mk path).isAbsolute do
      throw <| IO.userError "Prover worker requires absolute paths."
  checkAbsolute workerPath
  checkAbsolute assetsRoot
  checkAbsolute noteFile
  match request.validate with
  | .error _ => throw <| IO.userError "Invalid public prover request."
  | .ok () => pure ()
  if timeoutMs == 0 || timeoutMs > workerTimeoutMs then
    throw <| IO.userError "Invalid prover worker time limit."
  IO.FS.withTempFile fun handle requestPath => do
    checkAbsolute requestPath.toString
    handle.write request.encode.toUTF8
    handle.flush
    let args := #["--assets-root", assetsRoot, "--note-file", noteFile,
      "--request-file", requestPath.toString] ++
      match noteIndex with
      | none => #[]
      | some index => #["--note-index", index]
    let child ← try
      IO.Process.spawn {
        cmd := workerPath, args := args,
        stdin := .null, stdout := .piped, stderr := .null,
        inheritEnv := false,
        setsid := true
      }
    catch _ =>
      throw <| IO.userError "Prover worker could not start."
    try
      let output ← childOutput child timeoutMs
      if output.isEmpty || output[output.size - 1]! != 10 then
        throw <| IO.userError "Invalid prover worker response framing."
      let some line := String.fromUTF8? (output.extract 0 (output.size - 1))
        | throw <| IO.userError "Prover worker response is not UTF-8."
      let result ← match Result.decode line with
        | .ok result => pure result
        | .error _ => throw <| IO.userError "Invalid prover worker response."
      match acceptResponse request result with
      | .ok accepted => return accepted
      | .error _ => throw <| IO.userError "Prover worker proof was rejected."
    catch _ =>
      terminateChild child
      throw <| IO.userError "Prover worker failed or was rejected."

private def signerPublicLine (workerPath : String) (args : Array String)
    (timeoutMs : Nat) (limit : Nat := maxResponseBytes) : IO String := do
  if !(System.FilePath.mk workerPath).isAbsolute || timeoutMs == 0 ||
      timeoutMs > workerTimeoutMs || limit == 0 || limit > BatchMetadata.maxBytes then
    throw <| IO.userError "Invalid isolated signer invocation."
  let child ← try IO.Process.spawn {
      cmd := workerPath, args, stdin := .null, stdout := .piped, stderr := .null,
      inheritEnv := false, setsid := true }
    catch _ => throw <| IO.userError "Isolated signer could not start."
  try
    let output ← childOutput child timeoutMs limit
    if output.isEmpty || output[output.size - 1]! != 10 then
      throw <| IO.userError "Invalid isolated signer framing."
    let some raw := String.fromUTF8? (output.extract 0 (output.size - 1))
      | throw <| IO.userError "Invalid isolated signer encoding."
    return raw
  catch _ =>
    terminateChild child
    throw <| IO.userError "Isolated signer failed or was rejected."

/-- Bounded ordered inspection of every selected note. No raw note is ever
read by this parent; malformed/duplicate/mixed-asset batches fail closed. -/
def inspectBatchPrototype (workerPath noteFile : String) (chainId : Nat)
    (timeoutMs : Nat := workerTimeoutMs) : IO (Array Metadata) := do
  try
    if !(System.FilePath.mk noteFile).isAbsolute ||
        (chainId != 1 && chainId != 11155111) then
      throw <| IO.userError "Invalid prover batch inspection."
    let raw ← signerPublicLine workerPath
      #["--inspect-batch", "--note-file", noteFile, "--chain", toString chainId]
      timeoutMs BatchMetadata.maxBytes
    let items ← match BatchMetadata.decode raw with
      | .ok items => pure items
      | .error _ => throw <| IO.userError "Invalid prover batch metadata."
    if items.any (fun item => item.chainId != chainId) then
      throw <| IO.userError "Prover batch belongs to another chain."
    return items
  catch _ => throw <| IO.userError "Prover batch inspection failed or was rejected."

private def checkSignerIdentity (metadata : Metadata)
    (identity : ProverSignerWire.Identity) : Except String Unit := do
  metadata.validate
  identity.validate
  let sender ← NativeSigner.addressOfPublicKey identity.publicKey
  if sender != identity.sender ||
      identity.metadataHash != ProverSignerWire.metadataHash metadata then
    throw "Isolated signer identity differs from the selected note."

/-- Obtain only the legacy note-derived ephemeral public point/address. The
parent never opens the protected backup. This trusted worker is experimental. -/
def inspectSignerPrototype (workerPath noteFile : String) (metadata : Metadata)
    (noteIndex : Option String := none) (timeoutMs : Nat := workerTimeoutMs) :
    IO ProverSignerWire.Identity := do
  try
    if !(System.FilePath.mk noteFile).isAbsolute then
      throw <| IO.userError "Invalid isolated signer note path."
    let _ ← match metadata.validate with
      | .ok () => pure ()
      | .error _ => throw <| IO.userError "Invalid isolated signer selection."
    let args := #["--signer-identity", "--note-file", noteFile,
      "--chain", toString metadata.chainId] ++
      match noteIndex with | none => #[] | some index => #["--note-index", index]
    let raw ← signerPublicLine workerPath args timeoutMs
    let identity ← match ProverSignerWire.Identity.decode raw with
      | .ok result => pure result
      | .error _ => throw <| IO.userError "Invalid isolated signer response."
    match checkSignerIdentity metadata identity with
    | .ok () => return identity
    | .error _ => throw <| IO.userError "Invalid isolated signer identity."
  catch _ => throw <| IO.userError "Isolated signer inspection failed or was rejected."

/-- Verify both public ECDSA equations and recovery IDs against the exact
requested operation/auth digests and the previously selected ephemeral owner. -/
def acceptSignResponse (request : ProverSignerWire.SignRequest)
    (result : ProverSignerWire.SignedResult) : IO Unit := do
  let reject : IO Unit := throw <| IO.userError "Isolated signer response was rejected."
  match result.validateFor request with | .error _ => reject | .ok () => pure ()
  match checkSignerIdentity request.metadata result.identity with
  | .error _ => reject | .ok () => pure ()
  let authHash ← match request.authorizationHash with
    | .ok digest => pure digest
    | .error _ => throw <| IO.userError "Isolated signer response was rejected."
  unless (← NativeSigner.verifyPublicDigest result.identity.publicKey
      request.operationHash result.operationSignature) do reject
  unless (← NativeSigner.verifyPublicDigest result.identity.publicKey
      authHash result.authorizationSignature) do reject

/-- Decode the already parent-verified authorization into the bundler's exact
public transport shape. It is always selected-chain, pinned-delegate, nonce0. -/
def authorizationOf (request : ProverSignerWire.SignRequest)
    (result : ProverSignerWire.SignedResult) : Except String Bundler.Authorization := do
  result.validateFor request
  let sig := result.authorizationSignature
  let word (start : Nat) := (sig.extract start (start + 32)).data.foldl
    (fun n byte => n * 256 + byte.toNat) 0
  return {
    chainId := request.metadata.chainId, delegate := ProverSignerWire.delegate, nonce := 0
    r := word 0, s := word 32, yParity := sig[64]!.toNat - 27 }

/-- Return only public signatures after final review. The caller must journal
the complete signed operation and authorization before exposing either one. -/
def signPrototype (workerPath noteFile : String) (noteIndex : Option String)
    (request : ProverSignerWire.SignRequest) (timeoutMs : Nat := workerTimeoutMs) :
    IO ProverSignerWire.SignedResult := do
  try
    if !(System.FilePath.mk noteFile).isAbsolute then
      throw <| IO.userError "Invalid isolated signer note path."
    match request.validate with
    | .error _ => throw <| IO.userError "Invalid isolated signer request."
    | .ok () => pure ()
    IO.FS.withTempFile fun handle path => do
      if !path.isAbsolute then throw <| IO.userError "Invalid isolated signer request path."
      handle.write request.encode.toUTF8
      handle.flush
      let args := #["--sign", "--note-file", noteFile, "--request-file", path.toString] ++
        match noteIndex with | none => #[] | some index => #["--note-index", index]
      let raw ← signerPublicLine workerPath args timeoutMs
      let result ← match ProverSignerWire.SignedResult.decode raw with
        | .ok result => pure result
        | .error _ => throw <| IO.userError "Invalid isolated signer response."
      acceptSignResponse request result
      return result
  catch _ => throw <| IO.userError "Isolated signer failed or was rejected."

end Tornado.Runtime.ProverWorkerClient

#print axioms Tornado.Runtime.ProverWorkerClient.accepted_binds_review_and_verifies
