import Tornado.Protocol.ProverWorkerWire
import Tornado.Protocol.ProverSignerWire
import Tornado.Runtime.ProtectedIO
import Tornado.Runtime.Entropy
import Tornado.Runtime.NativeSigner

/-! Restricted effects for the actual isolated worker. The program cannot
construct a network request, arbitrary file path, write, or log operation.
The small native interpreter and OS primitives remain trusted. Typed proof
and signature bytes are cryptographic disclosures, not a zero-knowledge proof
about the implementation. Metadata associations are released only to the
trusted parent; this is not remote-RPC unlinkability. -/

namespace Tornado.Runtime.WorkerProgram

open Tornado.Protocol.ProverWorkerWire Tornado.Protocol.ProverSignerWire

inductive Mode where
  | inspect | inspectBatch | identity | sign | prove
  deriving BEq, DecidableEq, Inhabited

inductive Asset where
  | circuit | key | graph
  deriving BEq, DecidableEq, Inhabited

def Asset.suffix : Asset → String
  | .circuit => "/assets/proving/tornado-3ddd61dbff09caee.json.gz"
  | .key => "/assets/proving/tornadoProvingKey-8e2d2f22beafb5a9.bin.gz"
  | .graph => "/fixtures/witness-vm-selected-components.json"

inductive File where
  | note | request | asset (kind : Asset)
  deriving BEq, DecidableEq, Inhabited

def MayRead (mode : Mode) : File → Prop
  | .note => True
  | .request => mode = .sign ∨ mode = .prove
  | .asset _ => mode = .prove

/-- Only fixed configured slots can be read. There is no arbitrary-path
operation in a worker program. -/
inductive Program (mode : Mode) (α : Type) where
  | pure (value : α)
  | fail
  | read (file : File) (allowed : MayRead mode file)
      (next : ByteArray → Program mode α)
  | entropy32 (allowed : mode = .prove) (next : ByteArray → Program mode α)

def Program.bind (program : Program mode α) (f : α → Program mode β) : Program mode β :=
  match program with
  | .pure value => f value
  | .fail => .fail
  | .read file allowed next => .read file allowed (fun bytes => (next bytes).bind f)
  | .entropy32 allowed next => .entropy32 allowed (fun bytes => (next bytes).bind f)

instance : Monad (Program mode) where
  pure := .pure
  bind := Program.bind

def liftExcept (value : Except String α) : Program mode α :=
  match value with | .ok result => pure result | .error _ => .fail

def read (file : File) (allowed : MayRead mode file) : Program mode ByteArray :=
  .read file allowed .pure

def entropy32 (allowed : mode = .prove) : Program mode ByteArray :=
  .entropy32 allowed .pure

/-- These are the complete output constructors. No arbitrary Json, String,
note, mnemonic or byte-buffer output constructor exists. Result/signature
fields remain explicitly opaque cryptographic outputs. -/
inductive Response : Mode → Type where
  | metadata (value : Metadata) : Response .inspect
  | batch (value : Array Metadata) : Response .inspectBatch
  | identity (value : Identity) : Response .identity
  | signed (request : SignRequest) (value : SignedResult) : Response .sign
  | proof (request : Request) (value : Result) : Response .prove

def Response.encode : Response mode → String
  | .metadata value => value.encode
  | .batch value => BatchMetadata.encode value
  | .identity value => value.encode
  | .signed _ value => value.encode
  | .proof _ value => value.encode

/-- Reuse the strict canonical wire decoders at the actual release gate.
The request-bound output modes also repeat exact hash/signal binding checks. -/
def Response.wireValid : Response mode → Bool
  | .metadata value => (Metadata.decode value.encode).isOk
  | .batch value => (BatchMetadata.decode (BatchMetadata.encode value)).isOk
  | .identity value => (Identity.decode value.encode).isOk
  | .signed request value => (value.validateFor request).isOk &&
      (SignedResult.decode value.encode).isOk
  | .proof request value => (value.validateFor request).isOk &&
      (Result.decode value.encode).isOk

def Response.singleLine (response : Response mode) : Bool :=
  response.encode.toList.all (fun char => char != '\n' && char != '\r')

def Response.valid (response : Response mode) : Bool :=
  response.wireValid && response.singleLine

inductive Effect where
  | protect
  | read (file : File)
  | entropy32
  deriving BEq, DecidableEq, Inhabited

def Effect.allowed (mode : Mode) : Effect → Prop
  | .protect => True
  | .read file => MayRead mode file
  | .entropy32 => mode = .prove

/-- A record of interpreter calls, including failed calls. The trace contains
capability labels, never read bytes, note identifiers or secret-dependent errors. -/
structure Evaluation (mode : Mode) (α : Type) where
  value : Option α
  effects : List Effect
  confined : ∀ effect ∈ effects, effect.allowed mode

structure Execution (mode : Mode) (α : Type) extends Evaluation mode α where
  protectedFirst : effects.head? = some .protect

private def stopped : Evaluation mode α := ⟨none, [], by simp⟩

private def prepend (event : Effect) (allowed : event.allowed mode)
    (result : Evaluation mode α) : Evaluation mode α := {
  result with
  effects := event :: result.effects
  confined := by
    intro effect member
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst effect; exact allowed
    · exact result.confined effect member }

/-- The test seam and native interpreter expose only this restricted set of
operations. No opaque prover IO callback is accepted: all secret math is in
the pure program, and every read/entropy draw crosses an enumerated slot. -/
structure Backend where
  protect : IO Unit
  readNote : IO ByteArray
  readRequest : IO ByteArray
  readAsset : Asset → IO ByteArray
  entropy32 : IO ByteArray

private def Backend.read (backend : Backend) : File → IO ByteArray
  | .note => backend.readNote
  | .request => backend.readRequest
  | .asset kind => backend.readAsset kind

private def attempt (action : IO α) : IO (Option α) := do
  try return some (← action) catch _ => return none

private def evaluateCore (backend : Backend) (program : Program mode α) :
    IO (Evaluation mode α) := do
  match program with
  | .pure value => return ⟨some value, [], by simp⟩
  | .fail => return stopped
  | .read file allowed next =>
    let result ← match ← attempt (backend.read file) with
      | none => pure stopped
      | some bytes => evaluateCore backend (next bytes)
    return prepend (.read file) allowed result
  | .entropy32 allowed next =>
    let result ← match ← attempt backend.entropy32 with
      | none => pure stopped
      | some bytes => evaluateCore backend (next bytes)
    return prepend .entropy32 allowed result

/-- Core-dump suppression always precedes note/request/asset/entropy access.
Errors have no reflected String value and cannot become a terminal payload. -/
def evaluateWith (backend : Backend) (program : Program mode α) :
    IO (Execution mode α) := do
  let result ← match ← attempt backend.protect with
    | none => pure stopped
    | some () => evaluateCore backend program
  return { toEvaluation := prepend .protect trivial result, protectedFirst := rfl }

structure Scope where
  noteFile : String
  requestFile : Option String := none
  assetsRoot : Option String := none

def Scope.path (scope : Scope) : File → Option String
  | .note => some scope.noteFile
  | .request => scope.requestFile
  | .asset kind => scope.assetsRoot.map (· ++ kind.suffix)

private def failIO : IO α := throw <| IO.userError "Prover worker failed."

/-- Public input reads are capped in the actual handle loop. File metadata
and the OS's path/open semantics remain part of the native trust boundary. -/
private def boundedRead (path : String) (limit : Nat) : IO ByteArray := do
  let file := System.FilePath.mk path
  if !file.isAbsolute then failIO
  let metadata ← file.symlinkMetadata
  if metadata.type != .file || metadata.byteSize.toNat == 0 ||
      metadata.byteSize.toNat > limit then failIO
  let handle ← IO.FS.Handle.mk file .read
  let mut bytes := ByteArray.empty
  while bytes.size <= limit do
    let chunk ← handle.read (min 65536 (limit + 1 - bytes.size)).toUSize
    if chunk.isEmpty then break
    bytes := bytes ++ chunk
    if bytes.size > limit then failIO
  if bytes.isEmpty then failIO
  return bytes

private def absolute (path : String) : IO String := do
  if (System.FilePath.mk path).isAbsolute then return path
  return ((← IO.currentDir) / path).toString

/-- This is the small trusted IO interpretation. It opens the selected
protected note, selected bounded request, three fixed asset suffixes, and
kernel entropy. It contains no network, file-write, stdout or stderr call. -/
def nativeBackend (scope : Scope) : Backend := {
  protect := NativeSigner.disableWorkerCoreDumps
  readNote := do
    let some path := scope.path .note | failIO
    if !(System.FilePath.mk path).isAbsolute then failIO
    ProtectedIO.readPrivate path
  readRequest := do
    let some path := scope.path .request | failIO
    boundedRead path 4096
  readAsset := fun kind => do
    let some path := scope.path (.asset kind) | failIO
    boundedRead (← absolute path) (match kind with
      | .circuit => 4 * 1024 * 1024
      | .key => 32 * 1024 * 1024
      | .graph => 16 * 1024 * 1024)
  entropy32 := Entropy.readKernelRandom 32 }

def failureLine : String := "Prover worker failed.\n"

inductive Terminal (mode : Mode) where
  | success (response : Response mode) (valid : response.valid = true)
  | failure

/-- There is no unconditional declassification: every typed response passes
the strict canonical/binding gate, otherwise only the fixed failure is emitted. -/
def terminal (result : Option (Response mode)) : Terminal mode :=
  match result with
  | none => .failure
  | some response =>
    if valid : response.valid = true then .success response valid else .failure

def Terminal.stdout : Terminal mode → String
  | .success response _ => response.encode ++ "\n"
  | .failure => ""

def Terminal.stderr : Terminal mode → String
  | .success _ _ => ""
  | .failure => failureLine

def Terminal.exitCode : Terminal mode → UInt32
  | .success _ _ => 0
  | .failure => 1

/-- Only this final interpretation writes output. IO write failures stop
without a second output attempt; OS partial writes/crashes are not proved. -/
def emit (output : Terminal mode) : IO UInt32 := do
  try
    match output with
    | .success .. => (← IO.getStdout).putStr output.stdout
    | .failure => (← IO.getStderr).putStr output.stderr
    return output.exitCode
  catch _ => return 1

def run (scope : Scope) (program : Program mode (Response mode)) : IO UInt32 := do
  let result ← evaluateWith (nativeBackend scope) program
  emit (terminal result.value)

end Tornado.Runtime.WorkerProgram
