import Tornado.Cli.WithdrawProof
import Tornado.Protocol.ProverWorkerWire
import Tornado.Cli.WithdrawOne
import Tornado.Protocol.ProverSignerWire
import Tornado.Runtime.WorkerProgram

/-!
The actual isolated worker is a restricted effect program. Only the selected
note/request and three pinned asset slots may be read, and entropy is requested
only in proof mode. All parsing, note derivation, signing and proving below
are pure Except computations. The native interpreter owns the OS boundary.
Variable-time secret math, secret-dependent failure/timing and retained managed
memory remain outside the disclosure theorem. Metadata associations are
disclosed to the trusted parent, not declared harmless to a remote RPC.
-/

namespace Tornado.Cli.ProverWorker

open Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire
open Tornado.Runtime.WorkerProgram

def maxPublicRequestBytes : Nat := 4096

private def bad : String := "Prover worker failed."

private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def exactHexNat (raw : String) (size : Nat) : Except String Nat := do
  if !raw.startsWith "0x" then throw bad
  let bytes ← parseHexBytes raw
  if bytes.size != size then throw bad
  return wordNat bytes

private def metadataOf (selected : BackupIdentity) : Except String Metadata := do
  let metadata : Metadata := {
    chainId := chainNumber selected.note.pool.chainId
    pool := ← exactHexNat selected.note.pool.address 20
    commitment := ← exactHexNat selected.publicIdentity.commitment 32
    nullifierHash := ← exactHexNat selected.publicIdentity.nullifierHash 32
    amount := selected.note.pool.amount
    denomination := selected.note.pool.denomination
    asset := selected.note.pool.asset.symbol
    statusFileName := ← WithdrawOne.statusFileName selected.note }
  metadata.validate
  return metadata

private def text (bytes : ByteArray) : Except String String :=
  match String.fromUTF8? bytes with | some raw => .ok raw | none => .error bad

private def selectedProgram (chain : ChainId) (noteIndex : Option String) :
    Program mode BackupIdentity := do
  let bytes ← WorkerProgram.read .note trivial
  liftExcept <| History.selectNote (← liftExcept <| text bytes) chain noteIndex

def metadataProgram (chainId : Nat) (noteIndex : Option String) :
    Program .inspect Metadata := do
  let some chain := chainFromNat chainId | .fail
  liftExcept <| metadataOf (← selectedProgram chain noteIndex)

def batchProgram (chainId : Nat) : Program .inspectBatch (Array Metadata) := do
  let some chain := chainFromNat chainId | .fail
  let raw ← liftExcept <| text (← WorkerProgram.read .note trivial)
  let rawNotes ← liftExcept <| extractNoteStrings raw
  if rawNotes.isEmpty || rawNotes.length > 12 ||
      (raw.splitOn "tornado-").length != rawNotes.length + 1 then .fail
  let entries ← liftExcept <| parseDepositBackup raw chain
  let items ← liftExcept <| entries.toArray.mapM metadataOf
  liftExcept <| BatchMetadata.validate items
  return items

def publicRequestProgram : Program .prove Request := do
  liftExcept <| Request.decode
    (← liftExcept <| text (← WorkerProgram.read .request (Or.inr rfl)))

def signRequestProgram : Program .sign ProverSignerWire.SignRequest := do
  liftExcept <| ProverSignerWire.SignRequest.decode
    (← liftExcept <| text (← WorkerProgram.read .request (Or.inl rfl)))

private def ephemeralKey (selected : BackupIdentity) : Except String ByteArray := do
  let preimage ← parseHexBytes selected.note.preimage
  if preimage.size != 62 then throw bad
  let key := keccak256 (preimage.extract 0 31 ++ "KOHAKU7702".toUTF8)
  let scalar := wordNat key
  if scalar == 0 || scalar >= secp256k1Order then throw bad
  return key

private def signerIdentity (selected : BackupIdentity) (key : ByteArray) :
    Except String ProverSignerWire.Identity := do
  let publicKey ← secp256k1PublicKey key
  let sender ← NativeSigner.addressOfPublicKey publicKey
  let identity : ProverSignerWire.Identity := {
    metadataHash := ProverSignerWire.metadataHash (← metadataOf selected)
    publicKey, sender }
  identity.validate
  return identity

def identityProgram (chainId : Nat) (noteIndex : Option String) :
    Program .identity ProverSignerWire.Identity := do
  let some chain := chainFromNat chainId | .fail
  let selected ← selectedProgram chain noteIndex
  liftExcept <| signerIdentity selected (← liftExcept <| ephemeralKey selected)

/-- Secret-derived signatures are explicit opaque cryptographic outputs.
The request selects the public operation hash and pinned nonce-zero delegate. -/
private def signSelected (selected : BackupIdentity)
    (request : ProverSignerWire.SignRequest) :
    Except String ProverSignerWire.SignedResult := do
  request.validate
  if (← metadataOf selected) != request.metadata then throw bad
  let key ← ephemeralKey selected
  let identity ← signerIdentity selected key
  if identity.sender != request.expectedSender then throw bad
  let authHash ← request.authorizationHash
  let operation ← secp256k1SignDigest key request.operationHash
  let auth ← secp256k1SignDigest key authHash
  if operation.recovery >= 2 || auth.recovery >= 2 then throw bad
  let result : ProverSignerWire.SignedResult := {
    requestHash := request.hash, identity
    operationSignature := operation.bytes65
    authorizationSignature := auth.bytes65 }
  result.validateFor request
  return result

def signedProgram (noteIndex : Option String) (request : ProverSignerWire.SignRequest) :
    Program .sign ProverSignerWire.SignedResult := do
  liftExcept request.validate
  let some chain := chainFromNat request.metadata.chainId | .fail
  liftExcept <| signSelected (← selectedProgram chain noteIndex) request

private def noteForRequest (selected : BackupIdentity) (request : Request) :
    Except String TornadoSignatureNote := do
  let pool ← exactHexNat selected.note.pool.address 20
  let commitment ← exactHexNat selected.publicIdentity.commitment 32
  let nullifierHash ← exactHexNat selected.publicIdentity.nullifierHash 32
  if chainNumber selected.note.pool.chainId != request.chainId ||
      pool != request.pool || commitment != request.commitment ||
      nullifierHash != request.nullifierHash ||
      request.recipient == 0 || request.refund != 0 ||
      request.fee >= selected.note.pool.amount ||
      ((request.fee == 0) != (request.relayer == 0)) then throw bad
  let bytes ← parseHexBytes selected.note.preimage
  if bytes.size != 62 then throw bad
  return { nullifierBytes := bytes.extract 0 31,
           secretBytes := bytes.extract 31 62, commitment, nullifierHash }

/-- Every rejection draw is an explicit entropy32 effect. The exact loop is
shared with the runtime sampler and its finite distribution specification. -/
private def blindingProgram : Program .prove (ProofBlinding.Scalar × ProofBlinding.Scalar) :=
  ProofBlinding.samplePairLoop
    (do liftExcept <| ProofBlinding.admitCandidate (← WorkerProgram.entropy32 rfl))
    .fail ProofBlinding.maxAttempts

def proofProgram (noteIndex : Option String) (request : Request) :
    Program .prove Result := do
  liftExcept request.validate
  let some chain := chainFromNat request.chainId | .fail
  -- Authenticate large public assets before reading the spendable note.
  let circuit ← WorkerProgram.read (.asset .circuit) rfl
  let key ← WorkerProgram.read (.asset .key) rfl
  let graph ← liftExcept <| text (← WorkerProgram.read (.asset .graph) rfl)
  let assets ← liftExcept <| ClassicProofPipeline.loadBundled circuit key graph
  let selected ← selectedProgram chain noteIndex
  let note ← liftExcept <| noteForRequest selected request
  let path : MimcProof := ⟨request.leafIndex, request.root,
    request.siblings, request.pathIndices⟩
  let withdrawal : TornadoWitness.WithdrawalInput := {
    note, proof := path, expectedRoot := request.root,
    recipient := request.recipient, relayer := request.relayer,
    fee := request.fee, refund := request.refund }
  let _ ← liftExcept <| TornadoWitness.prepareInputPrefix withdrawal
  let (r, s) ← blindingProgram
  let publicProof ← liftExcept <|
    ClassicProofPipeline.prove assets withdrawal r.value s.value
  let result : Result := {
    requestHash := request.hash, proof := publicProof.bytes, signals := publicProof.signals }
  liftExcept <| result.validateFor request
  return result

private def valueWith (scope : Scope) (program : Program mode α) : IO α := do
  let result ← WorkerProgram.evaluateWith (WorkerProgram.nativeBackend scope) program
  match result.value with
  | some value => return value
  | none => throw <| IO.userError bad

/-- Existing embedding APIs use the same restricted interpreter as the
executable. They return typed values and do not emit stdout/stderr. -/
def inspectSelected (noteFile : String) (chainId : Nat)
    (noteIndex : Option String) : IO Metadata :=
  valueWith { noteFile } (metadataProgram chainId noteIndex)

def inspectBatch (noteFile : String) (chainId : Nat) : IO (Array Metadata) :=
  valueWith { noteFile } (batchProgram chainId)

def readPublicRequest (path : String) : IO Request :=
  valueWith { noteFile := "/unused", requestFile := some path } publicRequestProgram

def readSignRequest (path : String) : IO ProverSignerWire.SignRequest :=
  valueWith { noteFile := "/unused", requestFile := some path } signRequestProgram

def inspectSigner (noteFile : String) (chainId : Nat) (noteIndex : Option String) :
    IO ProverSignerWire.Identity :=
  valueWith { noteFile } (identityProgram chainId noteIndex)

def signRequest (noteFile : String) (noteIndex : Option String)
    (request : ProverSignerWire.SignRequest) : IO ProverSignerWire.SignedResult :=
  valueWith { noteFile } (signedProgram noteIndex request)

def proveRequest (assetRoot noteFile : String) (noteIndex : Option String)
    (request : Request) : IO Result :=
  valueWith { noteFile, assetsRoot := some assetRoot } (proofProgram noteIndex request)

end Tornado.Cli.ProverWorker
