import Tornado.Cli.WithdrawProof
import Tornado.Protocol.ProverWorkerWire
import Tornado.Cli.WithdrawOne
import Tornado.Protocol.ProverSignerWire
import Tornado.Runtime.NativeSigner

/-!
An isolated, experimental Classic withdrawal prover. Its only input from the
parent is a bounded, canonical public request and a path to an existing
protected note backup. The note is read in this process; only public proof
material is returned. Experimental live use is explicitly opt-in: the Lean
witness, ephemeral signing and proving arithmetic are variable time and do not
zeroize secrets. Process exit is only a partial secret-lifetime boundary.

The caller must independently establish that the public Merkle root is a
current or otherwise acceptable root of the selected pool. This worker
checks membership in the supplied root, not consensus state or spent status.
-/

namespace Tornado.Cli.ProverWorker

open Tornado.Crypto Tornado.Domain Tornado.Protocol Tornado.Runtime
open Tornado.Protocol.ProverWorkerWire

def maxPublicRequestBytes : Nat := 4096

private def failed : IO α :=
  throw <| IO.userError "Prover worker failed."

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error _ => failed

private def wordNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def exactHexNat (raw : String) (size : Nat) : IO Nat := do
  if !raw.startsWith "0x" then failed
  let bytes ← checked <| parseHexBytes raw
  if bytes.size != size then failed
  return wordNat bytes

private def metadataOf (selected : BackupIdentity) : IO ProverWorkerWire.Metadata := do
  let metadata : ProverWorkerWire.Metadata := {
    chainId := chainNumber selected.note.pool.chainId
    pool := ← exactHexNat selected.note.pool.address 20
    commitment := ← exactHexNat selected.publicIdentity.commitment 32
    nullifierHash := ← exactHexNat selected.publicIdentity.nullifierHash 32
    amount := selected.note.pool.amount
    denomination := selected.note.pool.denomination
    asset := selected.note.pool.asset.symbol
    statusFileName := ← checked <| WithdrawOne.statusFileName selected.note }
  let _ ← checked metadata.validate
  return metadata

/-- Select a protected note and return only its catalog identity, public
commitment/nullifier hash and opaque keyed status label. The parent never
needs the note preimage to fetch history or choose the status-file path. -/
def inspectSelected (noteFile : String) (chainId : Nat)
    (noteIndex : Option String) : IO ProverWorkerWire.Metadata := do
  try
    let some chain := chainFromNat chainId | failed
    if !(System.FilePath.mk noteFile).isAbsolute then failed
    let selected ← WithdrawProof.readSelected noteFile chain noteIndex
    metadataOf selected
  catch _ => failed

/-- Inspect all notes without choosing a default. Every apparent `tornado-`
token must be a recognized, valid note; malformed trailing notes fail closed. -/
def inspectBatch (noteFile : String) (chainId : Nat) : IO (Array Metadata) := do
  try
    let some chain := chainFromNat chainId | failed
    if !(System.FilePath.mk noteFile).isAbsolute then failed
    let bytes ← ProtectedIO.readPrivate noteFile
    let some raw := String.fromUTF8? bytes | failed
    let rawNotes ← checked <| extractNoteStrings raw
    if rawNotes.isEmpty || rawNotes.length > 12 ||
        (raw.splitOn "tornado-").length != rawNotes.length + 1 then failed
    let entries ← checked <| parseDepositBackup raw chain
    let items ← entries.toArray.mapM metadataOf
    let _ ← checked <| BatchMetadata.validate items
    return items
  catch _ => failed

/-- Read no more than 4 KiB of the public request. The metadata check is a
    quick guard; the bounded handle read is the actual size enforcement. A
    symlink or non-regular file is rejected before opening it. -/
private def readPublicRecord (path : String) : IO String := do
  let file := System.FilePath.mk path
  if !file.isAbsolute then failed
  let metadata ← file.symlinkMetadata
  if metadata.type != .file || metadata.byteSize.toNat == 0 ||
      metadata.byteSize.toNat > maxPublicRequestBytes then failed
  let handle ← IO.FS.Handle.mk file .read
  let mut bytes := ByteArray.empty
  while bytes.size <= maxPublicRequestBytes do
    let remaining := maxPublicRequestBytes + 1 - bytes.size
    let chunk ← handle.read (min remaining 4096).toUSize
    if chunk.isEmpty then break
    bytes := bytes ++ chunk
    if bytes.size > maxPublicRequestBytes then failed
  if bytes.isEmpty then failed
  let some raw := String.fromUTF8? bytes | failed
  return raw

def readPublicRequest (path : String) : IO ProverWorkerWire.Request := do
  checked <| ProverWorkerWire.Request.decode (← readPublicRecord path)

def readSignRequest (path : String) : IO ProverSignerWire.SignRequest := do
  checked <| ProverSignerWire.SignRequest.decode (← readPublicRecord path)

private def ephemeralKey (selected : BackupIdentity) : IO ByteArray := do
  let preimage ← checked <| parseHexBytes selected.note.preimage
  if preimage.size != 62 then failed
  let key := keccak256 (preimage.extract 0 31 ++ "KOHAKU7702".toUTF8)
  let scalar := wordNat key
  if scalar == 0 || scalar >= secp256k1Order then failed
  return key

private def signerIdentity (selected : BackupIdentity) (key : ByteArray) :
    IO ProverSignerWire.Identity := do
  let publicKey ← checked <| secp256k1PublicKey key
  let sender ← checked <| NativeSigner.addressOfPublicKey publicKey
  let identity : ProverSignerWire.Identity := {
    metadataHash := ProverSignerWire.metadataHash (← metadataOf selected)
    publicKey, sender }
  let _ ← checked identity.validate
  return identity

/-- Return the note-derived ephemeral public identity before constructing the
reviewed operation. The private key remains in this isolated process. -/
def inspectSigner (noteFile : String) (chainId : Nat) (noteIndex : Option String) :
    IO ProverSignerWire.Identity := do
  try
    let some chain := chainFromNat chainId | failed
    if !(System.FilePath.mk noteFile).isAbsolute then failed
    let selected ← WithdrawProof.readSelected noteFile chain noteIndex
    signerIdentity selected (← ephemeralKey selected)
  catch _ => failed

/-- Sign exactly the reviewed operation digest and pinned chain/delegate,
nonce-zero authorization. No secret key is transmitted to the parent. -/
def signRequest (noteFile : String) (noteIndex : Option String)
    (request : ProverSignerWire.SignRequest) : IO ProverSignerWire.SignedResult := do
  try
    let _ ← checked request.validate
    let some chain := chainFromNat request.metadata.chainId | failed
    if !(System.FilePath.mk noteFile).isAbsolute then failed
    let selected ← WithdrawProof.readSelected noteFile chain noteIndex
    if (← metadataOf selected) != request.metadata then failed
    let key ← ephemeralKey selected
    let identity ← signerIdentity selected key
    if identity.sender != request.expectedSender then failed
    let authHash ← checked request.authorizationHash
    let operation ← checked <| secp256k1SignDigest key request.operationHash
    let auth ← checked <| secp256k1SignDigest key authHash
    if operation.recovery >= 2 || auth.recovery >= 2 then failed
    let result : ProverSignerWire.SignedResult := {
      requestHash := request.hash, identity
      operationSignature := operation.bytes65
      authorizationSignature := auth.bytes65 }
    let _ ← checked <| result.validateFor request
    return result
  catch _ => failed

private def noteForRequest (selected : BackupIdentity)
    (request : ProverWorkerWire.Request) : IO TornadoSignatureNote := do
  let pool ← exactHexNat selected.note.pool.address 20
  let commitment ← exactHexNat selected.publicIdentity.commitment 32
  let nullifierHash ← exactHexNat selected.publicIdentity.nullifierHash 32
  if chainNumber selected.note.pool.chainId != request.chainId ||
      pool != request.pool || commitment != request.commitment ||
      nullifierHash != request.nullifierHash ||
      request.recipient == 0 || request.refund != 0 ||
      request.fee >= selected.note.pool.amount ||
      ((request.fee == 0) != (request.relayer == 0)) then failed
  let bytes ← checked <| parseHexBytes selected.note.preimage
  if bytes.size != 62 then failed
  return { nullifierBytes := bytes.extract 0 31,
           secretBytes := bytes.extract 31 62,
           commitment, nullifierHash }

/-- Secret-bearing proof generation. Parser/prover exceptions are replaced
    with a fixed message before they can
    reach the executable's stderr. The response contains only public fields. -/
def proveRequest (assetRoot noteFile : String) (noteIndex : Option String)
    (request : ProverWorkerWire.Request) : IO ProverWorkerWire.Result := do
  try
    let _ ← checked <| request.validate
    let some chain := chainFromNat request.chainId | failed
    if !(System.FilePath.mk noteFile).isAbsolute then failed
    -- Authenticate large public assets before loading the spendable note.
    let assets ← WithdrawProof.loadAssets assetRoot
    let selected ← WithdrawProof.readSelected noteFile chain noteIndex
    let note ← noteForRequest selected request
    let path : MimcProof := ⟨request.leafIndex, request.root,
      request.siblings, request.pathIndices⟩
    let withdrawal : TornadoWitness.WithdrawalInput := {
      note, proof := path, expectedRoot := request.root,
      recipient := request.recipient, relayer := request.relayer,
      fee := request.fee, refund := request.refund }
    let _ ← checked <| TornadoWitness.prepareInputPrefix withdrawal
    let (r, s) ← ProofBlinding.samplePair
    let publicProof ← checked <|
      ClassicProofPipeline.prove assets withdrawal r.value s.value
    if publicProof.bytes.size != 256 ||
        publicProof.signals != request.publicSignals then failed
    return { requestHash := request.hash, proof := publicProof.bytes,
             signals := publicProof.signals }
  catch _ => failed

end Tornado.Cli.ProverWorker
