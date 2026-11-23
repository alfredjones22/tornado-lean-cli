import Tornado.Domain.Invoice

/-!
Pure parsing of a private backup into public deposit identities. The input may
contain secret notes and a seed phrase; callers must never print it or include
it in errors. This matches the pinned CLI's note-like token extraction,
same-asset rule and duplicate-nullifier guard for inspect/invoice commands.
-/

namespace Tornado.Domain

structure BackupIdentity where
  note : ParsedNote
  publicIdentity : NoteIdentity
  -- The nested note is spendable; keep it out of generic debug formatting.
  deriving BEq, Inhabited

def parseDepositBackup (input : String) (chainId : ChainId) :
    Except String (List BackupIdentity) := do
  let raw ← extractNoteStrings input
  let notes ← raw.mapM (parseNote · chainId)
  let some first := notes.head? | throw "No Tornado note strings were found in this file."
  if notes.any (fun note => note.pool.asset.symbol != first.pool.asset.symbol) then
    throw "Use notes of one asset per deposit session."
  let nullifiers := notes.map fun note => String.ofList (note.preimage.toList.take 62)
  if nullifiers.eraseDups.length != notes.length then
    throw "The backup contains duplicate notes or reused nullifiers."
  notes.mapM fun note => do
    return { note, publicIdentity := (← noteIdentity note) }

end Tornado.Domain
