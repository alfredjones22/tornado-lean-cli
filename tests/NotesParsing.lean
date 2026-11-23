import Lean
import Tornado.Domain.NoteIdentity

open Lean Tornado.Domain

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def stringField (json : Json) (name : String) : Except String String := do
  (← field json name).getStr?

private def arrayField (json : Json) (name : String) : Except String (Array Json) := do
  (← field json name).getArr?

private def checkVectors (root : Json) : Except String Nat := do
  let groups ← arrayField root "groups"
  let mut count := 0
  let mut rawNotes : List String := []
  for group in groups do
    let chainNumber ← (← field group "chainId").getNat?
    let some chainId := chainFromNat chainNumber | throw "Unsupported vector chain"
    let symbol ← stringField group "symbol"
    let notes ← arrayField group "notes"
    for note in notes do
      let raw ← stringField note "raw"
      let denomination ← stringField note "denomination"
      let address ← stringField note "pool"
      let parsed ← parseNote raw chainId
      if parsed.raw != raw || parsed.pool.denomination != denomination ||
          parsed.pool.asset.symbol != symbol || parsed.pool.address.toLower != address.toLower ||
          parsed.preimage.length != 124 then
        throw s!"Parsed note mismatch at vector {count}"
      let expectedCommitment ← stringField note "commitment"
      let expectedNullifier ← stringField note "nullifierHash"
      let identity ← noteIdentity parsed
      if identity.commitment != expectedCommitment || identity.nullifierHash != expectedNullifier then
        throw s!"Pedersen identifier mismatch at vector {count}"
      rawNotes := rawNotes ++ [raw]
      count := count + 1
  let extracted ← extractNoteStrings ("SEED PHRASE\npublic test words\nNOTES\n" ++
    String.intercalate "\n" rawNotes ++ "\nMETADATA\n")
  if extracted != rawNotes then throw "Backup extraction changed note order or bytes"
  let some first := rawNotes.head? | throw "No notes in fixture"
  if (parseNote first .sepolia).isOk then throw "Wrong-chain note accepted"
  if (parseNote (first.dropEnd 2).toString .mainnet).isOk then throw "Truncated note accepted"
  if (parseBatchNotes (first ++ "\n" ++ first) .mainnet).isOk then
    throw "Duplicate-nullifier batch accepted"
  if (extractNoteStrings ("x" ++ first)).isOk then throw "Word-prefixed note token accepted"
  if (extractNoteStrings ("-" ++ first)).isOk then throw "Hyphen-prefixed note token accepted"
  if (extractNoteStrings (first ++ "_suffix")).isOk then throw "Word-suffixed note token accepted"
  return count

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/seeded-note-vectors.json"
  let result := do
    let json ← Json.parse raw
    checkVectors json
  match result with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok count =>
      if count != 11 then
        IO.eprintln s!"Expected 11 pinned note vectors, found {count}"
        return 1
      IO.println s!"PASS: parsed and derived Pedersen identifiers for {count} pinned raw-note vectors; malformed-note cases rejected"
      return 0
