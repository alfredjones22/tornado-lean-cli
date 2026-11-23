import Tornado.Cli.ProverWorker

/-!
Standalone experimental process for Classic proof generation and note-derived
ephemeral signing. Live use requires explicit experimental acknowledgement.
Successful stdout is exactly one canonical, public JSON response line. All
failures print one fixed diagnostic without exception text or user input.
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

private def fail : IO UInt32 := do
  IO.eprintln "Prover worker failed."
  return 1

def run (args : List String) : IO UInt32 := do
  try
    let some options := parseOptions args | return (← fail)
    let some noteFile := options.noteFile | return (← fail)
    Tornado.Runtime.NativeSigner.disableWorkerCoreDumps
    if options.inspect || options.signerIdentity || options.inspectBatch then
      let modes := (if options.inspect then 1 else 0) +
        (if options.signerIdentity then 1 else 0) + (if options.inspectBatch then 1 else 0)
      if modes != 1 || options.sign ||
          options.assetsRoot.isSome || options.requestFile.isSome then return (← fail)
      let some chain := options.chain | return (← fail)
      let some chainId := chain.toNat? | return (← fail)
      if toString chainId != chain then return (← fail)
      if options.inspectBatch then
        if options.noteIndex.isSome then return (← fail)
        let metadata ← ProverWorker.inspectBatch noteFile chainId
        IO.println (Tornado.Protocol.ProverWorkerWire.BatchMetadata.encode metadata)
      else if options.inspect then
        let metadata ← ProverWorker.inspectSelected noteFile chainId options.noteIndex
        IO.println metadata.encode
      else
        let identity ← ProverWorker.inspectSigner noteFile chainId options.noteIndex
        IO.println identity.encode
      return 0
    if options.chain.isSome then return (← fail)
    let some requestFile := options.requestFile | return (← fail)
    if options.sign then
      if options.assetsRoot.isSome then return (← fail)
      let request ← ProverWorker.readSignRequest requestFile
      let result ← ProverWorker.signRequest noteFile options.noteIndex request
      IO.println result.encode
      return 0
    let some assetsRoot := options.assetsRoot | return (← fail)
    let request ← ProverWorker.readPublicRequest requestFile
    let result ← ProverWorker.proveRequest assetsRoot noteFile
      options.noteIndex request
    IO.println result.encode
    return 0
  catch _ => fail

end Tornado.Cli.ProverWorkerMain

def main (args : List String) : IO UInt32 :=
  Tornado.Cli.ProverWorkerMain.run args
