import Lean
import Tornado.Domain.NoteCreation

open Lean Tornado.Domain

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def stringField (json : Json) (name : String) : Except String String :=
  (field json name).bind Json.getStr?

private def noteUUIDEntropy (nonce : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for index in [0:16] do
    result := result.push ((index + nonce) % 256).toUInt8
  return result

private def checkIndependent (root : Json) : Except String Nat := do
  let vectors ← (← field root "vectors").getArr?
  let mut checked := 0
  for vector in vectors do
    let chainNumber ← (← field vector "chainId").getNat?
    let some chain := chainFromNat chainNumber | throw "Unknown vector chain"
    let denomination ← stringField vector "denomination"
    let symbol ← stringField vector "symbol"
    let some pool := poolFor chain denomination symbol | throw "Unknown vector pool"
    if pool.address != (← stringField vector "address") then
      throw "Pinned pool address changed"
    let nullifierKey ← parseHexBytes (← stringField vector "nullifierKey")
    let saltKey ← parseHexBytes (← stringField vector "saltKey")
    let uuidEntropy ← parseHexBytes (← stringField vector "uuidEntropy")
    let created ← independentNoteFromEntropy pool nullifierKey saltKey uuidEntropy
    let call ← field vector "depositCall"
    if created.preimage != (← stringField vector "preimage") ||
        created.raw != (← stringField vector "raw") ||
        created.commitment != (← stringField vector "commitment") ||
        created.nullifierHash != (← stringField vector "nullifierHash") ||
        created.call.to != (← stringField call "to") ||
        created.call.data != (← stringField call "data") ||
        toString created.call.value != (← stringField call "value") then
      throw "Native independent note differs from the pinned SDK vector"
    if created.id != "00010203-0405-4607-8809-0a0b0c0d0e0f" then
      throw "Native UUID differs from version-four formatting"
    let parsed ← parseNote created.raw chain
    let identity ← noteIdentity parsed
    if identity.commitment != created.commitment ||
        identity.nullifierHash != created.nullifierHash then
      throw "Generated note did not roundtrip through native parser and Pedersen"
    let backup ← formatDepositBackup [created]
    if backup != created.raw ++ "\n" then throw "Independent backup format differs"
    checked := checked + 1
  let some sample := poolFor .mainnet "0.01" | throw "No sample pool"
  let good ← parseHexBytes ("0x" ++ String.ofList (List.replicate 64 '0'))
  let uuid := noteUUIDEntropy 0
  if (independentNoteFromEntropy sample (good.extract 0 31) good uuid).isOk then
    throw "Short nullifier key was accepted"
  if (independentNoteFromEntropy sample good good (uuid.extract 0 15)).isOk then
    throw "Short UUID entropy was accepted"
  if (legacyCoalescedSecret good (2 ^ 64) 1).isOk then
    throw "Out-of-range chain was accepted"
  if (legacyCoalescedSecret good 1 (2 ^ 160)).isOk then
    throw "Out-of-range pool address was accepted"
  return checked

private def checkSeeded (root : Json) (expectedBackup : String) : Except String Nat := do
  let mnemonic ← stringField root "mnemonic"
  let groups ← (← field root "groups").getArr?
  let mut checked := 0
  for group in groups do
    let chainNumber ← (← field group "chainId").getNat?
    let some chain := chainFromNat chainNumber | throw "Unknown group chain"
    let symbol ← stringField group "symbol"
    let vectors ← (← field group "notes").getArr?
    let mut pools := []
    for vector in vectors do
      let denomination ← stringField vector "denomination"
      let some pool := poolFor chain denomination symbol | throw "Unknown seeded pool"
      pools := pools ++ [pool]
    let uuids := (List.range pools.length).map noteUUIDEntropy
    let notes ← seededNotesFromMnemonic pools mnemonic uuids
    if notes.length != vectors.size then throw "Seeded note count differs"
    for (note, index) in notes.zipIdx do
      let vector := vectors[index]!
      if note.nonce != some index ||
          note.raw != (← stringField vector "raw") ||
          note.commitment != (← stringField vector "commitment") ||
          note.nullifierHash != (← stringField vector "nullifierHash") then
        throw "Seeded session note differs from the pinned SDK"
      checked := checked + 1
    let backup ← formatDepositBackup notes (some mnemonic)
    if !backup.startsWith "------- SEED PHRASE (SECRET) --------\n" ||
        !backup.contains mnemonic ||
        !(notes.all (fun note => backup.contains note.raw)) then
      throw "Seeded backup omitted the phrase or a raw note"
    if checked == vectors.size && backup != expectedBackup then
      throw "Seeded backup differs from the pinned TypeScript formatter"
  if (seededNotesFromMnemonic [] mnemonic []).isOk then
    throw "Empty seeded session was accepted"
  let some sample := poolFor .mainnet "0.01" | throw "No sample seeded pool"
  let duplicateUUID := noteUUIDEntropy 0
  if (seededNotesFromMnemonic [sample, sample] mnemonic
      [duplicateUUID, duplicateUUID]).isOk then
    throw "Duplicate seeded-note UUID entropy was accepted"
  return checked

def main : IO UInt32 := do
  let independentRaw ← IO.FS.readFile "fixtures/note-creation-vectors.json"
  let seededRaw ← IO.FS.readFile "fixtures/seeded-note-vectors.json"
  let seededBackup ← IO.FS.readFile "fixtures/seeded-backup-format.txt"
  let result := do
    let independent ← Json.parse independentRaw
    let seeded ← Json.parse seededRaw
    let generated ← checkIndependent independent
    let recovered ← checkSeeded seeded seededBackup
    return (generated, recovered)
  match result with
  | .error error =>
    IO.eprintln error
    return 1
  | .ok (generated, recovered) =>
    if generated != 3 || recovered != 11 then
      IO.eprintln "Unexpected independent or seeded note vector count"
      return 1
    IO.println "PASS: 3 independent SDK note vectors, 11 seeded notes, backup format, and input rejection"
    return 0
