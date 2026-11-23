import Lean
import Tornado.Domain.Invoice

open Lean Tornado.Domain

private def field (json : Json) (name : String) : Except String Json := json.getObjVal? name
private def stringField (json : Json) (name : String) : Except String String :=
  (field json name).bind Json.getStr?

private def checkVectors (root : Json) : Except String Nat := do
  let groups ← (← field root "groups").getArr?
  let mut checked := 0
  if depositSelector != "b214faa5" then throw "Native deposit selector differs from viem."
  for group in groups do
    let chainNum ← (← field group "chainId").getNat?
    let some chain := chainFromNat chainNum | throw "Unsupported fixture chain."
    let notes ← (← field group "notes").getArr?
    for row in notes do
      let raw ← stringField row "raw"
      let expectedCommitment ← stringField row "commitment"
      let note ← parseNote raw chain
      let identity ← noteIdentity note
      if identity.commitment != expectedCommitment then throw "Native note commitment changed."
      let invoice ← invoiceForNote note.pool identity.commitment
      if invoice.contains note.preimage then throw "Invoice disclosed a spending preimage."
      let decoded ← parseInvoice invoice chain
      let expectedData := "0x" ++ depositSelector ++ (identity.commitment.drop 2).toString
      if decoded.commitment != identity.commitment || decoded.pool.address != note.pool.address ||
          decoded.call.to != note.pool.address || decoded.call.data != expectedData ||
          decoded.call.value != (if note.pool.asset.token.isSome then 0 else note.pool.amount) then
        throw "Native invoice or deposit call differs from pinned ABI format."
      checked := checked + 1
  let some samplePool := poolFor .mainnet "0.01" | throw "No ETH sample pool."
  let sample := "0x" ++ String.ofList (List.replicate 64 'a')
  let invoice ← invoiceForNote samplePool sample
  if (parseInvoice invoice .sepolia).isOk then throw "Wrong-chain invoice accepted."
  if (parseInvoice (invoice.dropEnd 2).toString .mainnet).isOk then throw "Truncated invoice accepted."
  if (invoiceForNote samplePool "0x1234").isOk then throw "Short commitment accepted."
  let nbsp := String.singleton (Char.ofNat 160)
  let trimmed ← parseInvoice (nbsp ++ invoice ++ nbsp) .mainnet
  if trimmed.commitment != sample then throw "JavaScript-compatible invoice whitespace was not trimmed."
  return checked

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/seeded-note-vectors.json"
  let result := do
    let json ← Json.parse raw
    checkVectors json
  match result with
  | .error error =>
      IO.eprintln error
      return 1
  | .ok checked =>
      if checked != 11 then
        IO.eprintln s!"Expected 11 invoices, found {checked}"
        return 1
      IO.println s!"PASS: {checked} native invoice and deposit ABI vectors"
      return 0
