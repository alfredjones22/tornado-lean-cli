import Lean
import Tornado.Spec.DepositBackupIntent

/-! Public synthetic and pinned compatibility inputs only. Failure messages
never include note text, mnemonic text, preimages or their encodings. -/
open Lean Tornado.Domain Tornado.Cli

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error _ => throw <| IO.userError "Backup regression check failed."

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

private def sameResult (left right : Except String String) : Bool :=
  match left, right with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def syntheticNote (pool : Pool) (index : Nat) : CreatedNote :=
  let preimage := Tornado.Crypto.bytesToHex
    ((ByteArray.mk (Array.replicate 30 0)).push index.toUInt8 ++
      ByteArray.mk (Array.replicate 31 0))
  { raw := renderNoteText pool preimage, preimage, pool,
    commitment := "", nullifierHash := "", id := "public-test", nonce := some index,
    call := default }

def main : IO UInt32 := do
  let vectorRoot ← checked <| Json.parse (← IO.FS.readFile "fixtures/note-creation-vectors.json")
  let vectors ← checked <| (← checked <| vectorRoot.getObjVal? "vectors").getArr?
  let raw ← checked <| (← checked <| vectors[0]!.getObjVal? "raw").getStr?
  let parsed ← checked <| parseNote raw .mainnet
  let identity ← checked <| noteIdentity parsed
  let plain := raw ++ "\n"
  let backup ← checked <| parseDepositBackup plain .mainnet
  require (backup.length == 1 && backup[0]!.publicIdentity == identity)
    "Plain backup did not recompute the exact native public identity."
  let fundingItems ← checked <| DepositMulti.publicItems plain .mainnet
  require (fundingItems.size == 1 && fundingItems[0]!.commitment.size == 32)
    "Actual private-backup funding projection failed."
  let seededText ← IO.FS.readFile "fixtures/seeded-backup-format.txt"
  let seeded ← checked <| parseCanonicalBackupText seededText .mainnet
  let recovered ← checked <| parseBackupNotes seededText .mainnet
  require (!seeded.isEmpty && seeded == recovered)
    "Pinned seeded backup did not use the exact-format canonical parser."
  let pool := parsed.pool
  let synthetic := (List.range 100).map (syntheticNote pool)
  for count in [1, 2, 100] do
    let notes := synthetic.take count
    for phrase in [none, some "", some "public synthetic mnemonic words", some "line one\nline two"] do
      require (sameResult (formatDepositBackup notes phrase) (legacyFormatDepositBackup notes phrase))
        "Canonical line formatter changed the preserved backup bytes."
  require (sameResult (formatDepositBackup [] none) (legacyFormatDepositBackup [] none) &&
    sameResult (formatDepositBackup [] (some "public")) (legacyFormatDepositBackup [] (some "public")))
    "Empty-session formatting policy changed."
  let phrase := "public synthetic mnemonic words"
  let generated ← checked <| formatDepositBackup synthetic (some phrase)
  let canonicalHundred ← checked <| parseCanonicalBackupText generated .mainnet
  require (canonicalHundred.length == 100 && canonicalHundred.map (·.raw) == synthetic.map (·.raw))
    "Maximum supported seeded backup lost note order or exceeded the parser stack."
  let plainHundred ← checked <| formatDepositBackup synthetic none
  require ((← checked <| parseCanonicalBackupText plainHundred .mainnet).length == 100)
    "Maximum supported plain backup exceeded the canonical line bound."
  let tooMany ← checked <| formatDepositBackup (synthetic ++ [syntheticNote pool 100]) none
  require (!(DepositMulti.publicItems tooMany .mainnet).isOk)
    "More than 100 notes reached public-identity hashing."
  let tamperedMetadata := generated.replace "Note nonces: 0," "Note nonces: 9,"
  require (!(parseCanonicalBackupText tamperedMetadata .mainnet).isOk &&
    (← checked <| parseBackupNotes tamperedMetadata .mainnet).length == 100)
    "Metadata certification and legacy raw-note recovery were conflated."
  let extra := syntheticNote pool 101
  let trailing := generated ++ extra.raw ++ "\n"
  require (!(parseCanonicalBackupText trailing .mainnet).isOk &&
    (← checked <| parseBackupNotes trailing .mainnet).length == 101)
    "A trailing recoverable note was silently ignored."
  let embedded := generated.replace phrase (phrase ++ " " ++ extra.raw)
  require (!(parseCanonicalBackupText embedded .mainnet).isOk &&
    (← checked <| parseBackupNotes embedded .mainnet).length == 101)
    "An embedded note token was silently ignored by the seed grammar."
  let decorated := "Legacy annotation: [" ++ raw ++ "]\nEnd."
  require ((← checked <| parseBackupNotes decorated .mainnet).length == 1)
    "Unchanged legacy token-extraction fallback rejected a saved backup."
  require (!(parseDepositBackup (plain ++ plain) .mainnet).isOk &&
    !(parseBackupNotes plain .sepolia).isOk)
    "Duplicate/reused-nullifier or wrong-chain backup was accepted."
  let huge := String.ofList (List.replicate (1024 * 1024) 'x')
  require (!(parseCanonicalNote huge .mainnet).isOk)
    "Large malformed canonical note was accepted or exhausted the parser stack."
  IO.println "PASS: constructive private-backup projection, exact seeded metadata, preserved formatter and legacy recovery, 100-note/1MiB boundaries, and canonical extra-token rejection"
  return 0
