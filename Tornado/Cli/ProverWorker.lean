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

/-- The actual worker's final pure stage. Its certificate bridge below
retains the original proving source while this result contains public data only. -/
def finishProof (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (r s : Nat) (request : Request) :
    Except String Result :=
  match ClassicProofPipeline.prove assets withdrawal r s with
  | .error message => .error message
  | .ok publicProof =>
    let result : Result := {
      requestHash := request.hash, proof := publicProof.bytes, signals := publicProof.signals }
    match result.validateFor request with
    | .error message => .error message
    | .ok _ => .ok result

/-- The extraction preserves the actual restricted worker tail, including
failure behavior. Only a pure Except computation has been grouped. -/
theorem finishProof_preserves_worker_tail (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (r s : Nat) (request : Request) :
    (liftExcept (finishProof assets withdrawal r s request) : Program .prove Result) =
      (do
        let publicProof ← liftExcept <| ClassicProofPipeline.prove assets withdrawal r s
        let result : Result := {
          requestHash := request.hash, proof := publicProof.bytes, signals := publicProof.signals }
        liftExcept <| result.validateFor request
        return result) := by
  cases hp : ClassicProofPipeline.prove assets withdrawal r s with
  | error message => simp [finishProof, hp, WorkerProgram.liftExcept, Bind.bind, Program.bind]
  | ok publicProof =>
    cases hv : (Result.mk request.hash publicProof.bytes publicProof.signals).validateFor request with
    | error message => simp [finishProof, hp, hv, WorkerProgram.liftExcept, Bind.bind, Program.bind]
    | ok unitValue =>
      cases unitValue
      simp [finishProof, hp, hv, WorkerProgram.liftExcept, Bind.bind, Program.bind]

/-- Worker-result success carries the exact original native construction,
not a caller-supplied verifier-acceptance premise. -/
theorem finishProof_success_from_original (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (r s : Nat) (request : Request)
    (result : Result) (success : finishProof assets withdrawal r s request = .ok result) :
    ∃ publicProof : ClassicProofPipeline.PublicProof assets.circuit,
      ClassicProofPipeline.prove assets withdrawal r s = .ok publicProof ∧
      ClassicProofPipeline.OriginalConstruction assets withdrawal r s publicProof ∧
      result.requestHash = request.hash ∧ result.proof = publicProof.bytes ∧
      result.signals = (ClassicProofPipeline.ReviewedPublic.ofWithdrawal withdrawal).signals ∧
      result.validateFor request = .ok () := by
  unfold finishProof at success
  split at success
  · cases success
  · rename_i publicProof hp
    dsimp only at success
    split at success
    · cases success
    · rename_i unitValue hv
      cases unitValue
      cases success
      have built := ClassicProofPipeline.prove_success_from_original assets withdrawal r s publicProof hp
      exact ⟨publicProof, hp, built, rfl, rfl, built.signalsOriginal, hv⟩

/-- The exact public serialization emitted from this worker stage retains
its proof-byte origin and six original reviewed withdrawal values. -/
theorem finishProof_success_serialization (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (r s : Nat) (request : Request)
    (result : Result) (success : finishProof assets withdrawal r s request = .ok result) :
    ∃ publicProof : ClassicProofPipeline.PublicProof assets.circuit,
      ClassicProofPipeline.OriginalConstruction assets withdrawal r s publicProof ∧
      result.encode = (Result.mk request.hash publicProof.bytes
        (ClassicProofPipeline.ReviewedPublic.ofWithdrawal withdrawal).signals).encode := by
  obtain ⟨publicProof, _, built, requestBound, proofBound, signalsBound, _⟩ :=
    finishProof_success_from_original assets withdrawal r s request result success
  refine ⟨publicProof, built, ?_⟩
  cases result
  simp_all

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
  liftExcept <| finishProof assets withdrawal r.value s.value request

/-- A finite successful branch of the actual restricted program. Read and
entropy replies are explicit witnesses; this is not a claim about physical IO. -/
inductive SourceReturns : Program mode α → α → Prop where
  | done (value : α) : SourceReturns (.pure value) value
  | read (file allowed next bytes value) : SourceReturns (next bytes) value →
      SourceReturns (.read file allowed next) value
  | entropy (allowed next bytes value) : SourceReturns (next bytes) value →
      SourceReturns (.entropy32 allowed next) value

private theorem sourceReturns_bind (program : Program mode α) (next : α → Program mode β)
    (result : β) (returned : SourceReturns (program.bind next) result) :
    ∃ value, SourceReturns program value ∧ SourceReturns (next value) result := by
  induction program with
  | pure value => exact ⟨value, .done value, returned⟩
  | fail => cases returned
  | read file allowed continuation ih =>
    cases returned with
    | read _ _ _ bytes _ child =>
      obtain ⟨value, first, last⟩ := ih bytes child
      exact ⟨value, .read file allowed continuation bytes value first, last⟩
  | entropy32 allowed continuation ih =>
    cases returned with
    | entropy _ _ bytes _ child =>
      obtain ⟨value, first, last⟩ := ih bytes child
      exact ⟨value, .entropy allowed continuation bytes value first, last⟩

private theorem sourceReturns_liftExcept (attempt : Except String α) (result : α)
    (returned : SourceReturns (WorkerProgram.liftExcept attempt : Program mode α) result) :
    attempt = .ok result := by
  cases attempt with
  | error message => cases returned
  | ok value => cases returned; rfl

/-- Every finite successful branch of the actual worker proof program
retains the native construction source of its released bytes. -/
theorem proofProgram_returns_native_construction (noteIndex : Option String) (request : Request)
    (result : Result) (returned : SourceReturns (proofProgram noteIndex request) result) :
    ∃ (assets : ClassicProofPipeline.PinnedAssets) (withdrawal : TornadoWitness.WithdrawalInput)
      (r s : Nat) (publicProof : ClassicProofPipeline.PublicProof assets.circuit),
      ClassicProofPipeline.OriginalConstruction assets withdrawal r s publicProof ∧
      result.requestHash = request.hash ∧ result.proof = publicProof.bytes ∧
      result.signals = (ClassicProofPipeline.ReviewedPublic.ofWithdrawal withdrawal).signals ∧
      result.validateFor request = .ok () := by
  unfold proofProgram at returned
  obtain ⟨_, _, returned⟩ := sourceReturns_bind _ _ _ returned
  split at returned
  · rename_i chain chainFound
    obtain ⟨circuit, _, returned⟩ := sourceReturns_bind _ _ _ returned
    obtain ⟨key, _, returned⟩ := sourceReturns_bind _ _ _ returned
    obtain ⟨graphBytes, _, returned⟩ := sourceReturns_bind _ _ _ returned
    obtain ⟨graph, _, returned⟩ := sourceReturns_bind _ _ _ returned
    obtain ⟨assets, _, returned⟩ := sourceReturns_bind _ _ _ returned
    obtain ⟨selected, _, returned⟩ := sourceReturns_bind _ _ _ returned
    obtain ⟨note, _, returned⟩ := sourceReturns_bind _ _ _ returned
    try dsimp only at returned
    obtain ⟨_, _, returned⟩ := sourceReturns_bind _ _ _ returned
    obtain ⟨blinding, _, returned⟩ := sourceReturns_bind _ _ _ returned
    rcases blinding with ⟨r, s⟩
    have completed := sourceReturns_liftExcept _ _ returned
    obtain ⟨publicProof, _, built, requestBound, proofBound, signalsBound, validated⟩ :=
      finishProof_success_from_original _ _ _ _ _ _ completed
    exact ⟨assets, _, r.value, s.value, publicProof, built,
      requestBound, proofBound, signalsBound, validated⟩
  · cases returned

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

#print axioms Tornado.Cli.ProverWorker.finishProof_success_from_original
#print axioms Tornado.Cli.ProverWorker.finishProof_success_serialization

#print axioms Tornado.Cli.ProverWorker.finishProof_preserves_worker_tail

#print axioms Tornado.Cli.ProverWorker.sourceReturns_bind
#print axioms Tornado.Cli.ProverWorker.sourceReturns_liftExcept
#print axioms Tornado.Cli.ProverWorker.proofProgram_returns_native_construction
