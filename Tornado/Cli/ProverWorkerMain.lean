import Tornado.Cli.ProverWorker

/-!
Standalone experimental process for Classic proof generation and note-derived
signing. Its actual command dispatch constructs the restricted worker program.
The typed release gate emits canonical JSON for the trusted parent or a fixed
failure; it does not imply remote unlinkability or secret-safe arithmetic.
-/

namespace Tornado.Cli.ProverWorkerMain

private structure Options where
  inspect : Bool := false
  inspectBatch : Bool := false
  signerIdentity : Bool := false
  sign : Bool := false
  chain : Option String := none
  assetsRoot : Option String := none
  noteFile : Option String := none
  requestFile : Option String := none
  noteIndex : Option String := none
  deriving Inhabited

private partial def parseOptions (args : List String) (options : Options := {}) :
    Option Options :=
  match args with
  | [] => some options
  | "--inspect" :: rest =>
    if options.inspect then none else parseOptions rest { options with inspect := true }
  | "--inspect-batch" :: rest =>
    if options.inspectBatch then none else parseOptions rest { options with inspectBatch := true }
  | "--signer-identity" :: rest =>
    if options.signerIdentity then none
    else parseOptions rest { options with signerIdentity := true }
  | "--sign" :: rest =>
    if options.sign then none else parseOptions rest { options with sign := true }
  | "--chain" :: value :: rest =>
    if options.chain.isSome || value.isEmpty then none
    else parseOptions rest { options with chain := some value }
  | "--assets-root" :: value :: rest =>
    if options.assetsRoot.isSome || value.isEmpty then none
    else parseOptions rest { options with assetsRoot := some value }
  | "--note-file" :: value :: rest =>
    if options.noteFile.isSome || value.isEmpty then none
    else parseOptions rest { options with noteFile := some value }
  | "--request-file" :: value :: rest =>
    if options.requestFile.isSome || value.isEmpty then none
    else parseOptions rest { options with requestFile := some value }
  | "--note-index" :: value :: rest =>
    if options.noteIndex.isSome || value.isEmpty then none
    else parseOptions rest { options with noteIndex := some value }
  | _ => none


open Tornado.Runtime.WorkerProgram

/-- The selected mode indexes both permitted reads and the exact response
constructor. Command-line strings never become output payload constructors. -/
structure Invocation where
  mode : Mode
  scope : Scope
  program : Program mode (Response mode)

def invocation (args : List String) : Option Invocation := do
  let options ← parseOptions args
  let noteFile ← options.noteFile
  let scope : Scope := {
    noteFile, requestFile := options.requestFile, assetsRoot := options.assetsRoot }
  if options.inspect || options.signerIdentity || options.inspectBatch then
    let modes := (if options.inspect then 1 else 0) +
      (if options.signerIdentity then 1 else 0) + (if options.inspectBatch then 1 else 0)
    if modes != 1 || options.sign || options.assetsRoot.isSome ||
        options.requestFile.isSome then none
    let chain ← options.chain
    let chainId ← chain.toNat?
    if toString chainId != chain then none
    if options.inspectBatch then
      if options.noteIndex.isSome then none
      return ⟨.inspectBatch, scope, do
        return .batch (← ProverWorker.batchProgram chainId)⟩
    if options.inspect then
      return ⟨.inspect, scope, do
        return .metadata (← ProverWorker.metadataProgram chainId options.noteIndex)⟩
    return ⟨.identity, scope, do
      return .identity (← ProverWorker.identityProgram chainId options.noteIndex)⟩
  if options.chain.isSome || options.requestFile.isNone then none
  if options.sign then
    if options.assetsRoot.isSome then none
    return ⟨.sign, scope, do
      let request ← ProverWorker.signRequestProgram
      return .signed request (← ProverWorker.signedProgram options.noteIndex request)⟩
  if options.assetsRoot.isNone then none
  return ⟨.prove, scope, do
    let request ← ProverWorker.publicRequestProgram
    return .proof request (← ProverWorker.proofProgram options.noteIndex request)⟩

def run (args : List String) : IO UInt32 :=
  match invocation args with
  | none => emit (Terminal.failure (mode := .inspect))
  | some call => Tornado.Runtime.WorkerProgram.run call.scope call.program

end Tornado.Cli.ProverWorkerMain

def main (args : List String) : IO UInt32 :=
  Tornado.Cli.ProverWorkerMain.run args
