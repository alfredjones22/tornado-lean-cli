import Tornado.Domain.Catalog

/-!
Native parsing of Classic Tornado note strings and selected note batches.
This module deliberately does not claim to compute commitments or nullifier
hashes: those require the separate Pedersen implementation and vectors.
-/

namespace Tornado.Domain

structure ParsedNote where
  raw : String
  preimage : String
  pool : Pool
  -- This type carries the full spendable note. Do not derive Repr: a debug
  -- print would disclose the nullifier and secret.
  deriving BEq, Inhabited

def maxMultiNotes : Nat := 12

private def asciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def asciiAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
private def asciiAlphaNum (c : Char) : Bool := asciiAlpha c || asciiDigit c
private def asciiWord (c : Char) : Bool := asciiAlphaNum c || c == '_'
private def asciiHex (c : Char) : Bool :=
  asciiDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def nonemptyAll (s : String) (predicate : Char → Bool) : Bool :=
  !s.isEmpty && s.toList.all predicate

private def noteLines (input : String) : List String :=
  (input.splitOn "\n").map jsTrim |>.filter (fun line => !line.isEmpty)

def parseNote (input : String) (chainId : ChainId) : Except String ParsedNote := do
  let lines := noteLines input
  if lines.isEmpty then throw "Provide one withdrawal note."
  if lines.length != 1 then throw "Provide one note at a time for a single-note withdrawal."
  let raw := lines.head!
  let [tag, symbol, denomination, chainText, secret] := raw.splitOn "-"
    | throw "This is not a supported withdrawal note."
  if tag != "tornado" || !nonemptyAll symbol asciiAlphaNum ||
      !nonemptyAll denomination (fun c => asciiDigit c || c == '.') ||
      !(chainText == "1" || chainText == "11155111") ||
      !(secret.startsWith "0x") || secret.length != 126 ||
      !(secret.toList.drop 2).all asciiHex then
    throw "This is not a supported withdrawal note."
  if chainText != toString (chainNumber chainId) then
    throw "This note belongs to a different network."
  let some pool := poolFor chainId denomination symbol
    | throw "This note uses an unavailable denomination."
  return { raw, pool, preimage := String.ofList (secret.toList.drop 2) |>.toLower }

def parseBatchNotes (input : String) (chainId : ChainId) (minimum : Nat := 2) : Except String (List ParsedNote) := do
  let lines := noteLines input
  if minimum == 0 || minimum > maxMultiNotes then throw "Invalid minimum note count."
  if lines.length < minimum || lines.length > maxMultiNotes then
    throw s!"Use {minimum}–{maxMultiNotes} notes for this smart-account withdrawal."
  let notes ← lines.mapM (fun line => parseNote line chainId)
  let first := notes.head!
  if notes.any (fun note => note.pool.asset.symbol != first.pool.asset.symbol) then
    throw "Use notes of one asset per batch. Different denominations are allowed."
  let nullifiers := notes.map (fun note => String.ofList (note.preimage.toList.take 62))
  if nullifiers.eraseDups.length != notes.length then
    throw "The batch contains duplicate notes or reused nullifiers."
  return notes

/-! Match the TS backup extractor's permissive note-like regex. It does not
validate pool, chain, or 62-byte secret length; parseNote does that later. -/
private def matchNoteAt (chars : List Char) (start : Nat) : Option (Nat × String) := do
  let before := if start == 0 then none else chars[start - 1]?
  if before.any (fun c => asciiWord c || c == '-') then none else pure ()
  let notePrefix := "tornado-".toList
  let remaining := chars.drop start
  if remaining.take notePrefix.length != notePrefix then none else pure ()
  let afterPrefix := remaining.drop notePrefix.length
  let symbol := afterPrefix.takeWhile asciiAlphaNum
  if symbol.isEmpty then none else pure ()
  let afterSymbol := afterPrefix.drop symbol.length
  if afterSymbol.head? != some '-' then none else pure ()
  let afterDash1 := afterSymbol.drop 1
  let denomination := afterDash1.takeWhile (fun c => asciiDigit c || c == '.')
  if denomination.isEmpty then none else pure ()
  let afterDenomination := afterDash1.drop denomination.length
  if afterDenomination.head? != some '-' then none else pure ()
  let afterDash2 := afterDenomination.drop 1
  let chain := afterDash2.takeWhile asciiDigit
  if chain.isEmpty then none else pure ()
  let afterChain := afterDash2.drop chain.length
  if afterChain.take 3 != "-0x".toList then none else pure ()
  let afterHexPrefix := afterChain.drop 3
  let secret := afterHexPrefix.takeWhile asciiAlphaNum
  if secret.isEmpty then none else pure ()
  let trailing := afterHexPrefix.drop secret.length
  if trailing.head?.any (fun c => asciiWord c || c == '-') then none else pure ()
  let endIndex := chars.length - trailing.length
  return (endIndex, String.ofList ((chars.drop start).take (endIndex - start)))

def extractNoteStrings (input : String) : Except String (List String) := do
  let chars := input.toList
  let mut matchedUntil := 0
  let mut notes : List String := []
  for index in [0:chars.length] do
    if index < matchedUntil then continue
    if let some (endIndex, raw) := matchNoteAt chars index then
      matchedUntil := endIndex
      notes := notes ++ [raw]
  if notes.isEmpty then throw "No Tornado note strings were found in this file."
  return notes

end Tornado.Domain
