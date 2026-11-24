import Std
import LeanCrypto.Hex
import Tornado.Domain.Catalog

namespace Tornado.Domain.CanonicalText

def split (separator : Char) : List Char → List (List Char)
  | [] => [[]]
  | char :: rest =>
      if char = separator then [] :: split separator rest
      else match split separator rest with
        | [] => [[char]]
        | first :: tail => (char :: first) :: tail

theorem split_nonempty (separator : Char) (text : List Char) : split separator text ≠ [] := by
  cases text with
  | nil => simp [split]
  | cons char rest =>
    simp only [split]
    split
    · simp
    · cases split separator rest <;> simp

theorem split_append_separator (separator : Char) (left right : List Char)
    (clean : ∀ char ∈ left, char ≠ separator) :
    split separator (left ++ separator :: right) = left :: split separator right := by
  induction left with
  | nil => simp [split]
  | cons char rest ih =>
    have hc : char ≠ separator := clean char (by simp)
    have hr : ∀ char ∈ rest, char ≠ separator := fun x hx => clean x (by simp [hx])
    simp only [List.cons_append, split, if_neg hc, ih hr]

theorem split_clean (separator : Char) (text : List Char)
    (clean : ∀ char ∈ text, char ≠ separator) : split separator text = [text] := by
  induction text with
  | nil => rfl
  | cons char rest ih =>
    have hc : char ≠ separator := clean char (by simp)
    have hr : ∀ char ∈ rest, char ≠ separator := fun x hx => clean x (by simp [hx])
    simp only [split, if_neg hc, ih hr]

def join (separator : Char) : List (List Char) → List Char
  | [] => []
  | [last] => last
  | first :: second :: rest => first ++ separator :: join separator (second :: rest)

theorem split_join (separator : Char) (parts : List (List Char))
    (nonempty : parts ≠ [])
    (clean : ∀ part ∈ parts, ∀ char ∈ part, char ≠ separator) :
    split separator (join separator parts) = parts := by
  induction parts with
  | nil => contradiction
  | cons first rest ih =>
    cases rest with
    | nil => exact split_clean separator first (clean first (by simp))
    | cons second rest =>
      simp only [join]
      rw [split_append_separator separator first _ (clean first (by simp))]
      congr 1
      apply ih (by simp)
      intro part member
      exact clean part (by simp [member])

/-- Tail-recursive executable splitter. The structural definition above is
only the proof reference; user-controlled backup text uses this loop. -/
def splitLoop (separator : Char) : List Char → List Char → List (List Char) → List (List Char)
  | [], current, parts => (current.reverse :: parts).reverse
  | char :: rest, current, parts =>
      if char = separator then splitLoop separator rest [] (current.reverse :: parts)
      else splitLoop separator rest (char :: current) parts

def prependPart (current : List Char) : List (List Char) → List (List Char)
  | [] => []
  | first :: rest => (current ++ first) :: rest

theorem splitLoop_reference (separator : Char) (text current : List Char)
    (parts : List (List Char)) :
    splitLoop separator text current parts =
      parts.reverse ++ prependPart current.reverse (split separator text) := by
  induction text generalizing current parts with
  | nil => simp [splitLoop, split, prependPart]
  | cons char rest ih =>
    by_cases hc : char = separator
    · subst char
      simp only [splitLoop, split, ite_true, ih, List.reverse_cons, List.reverse_nil,
        prependPart, List.append_nil]
      cases hs : split separator rest with
      | nil => exact False.elim (split_nonempty separator rest hs)
      | cons first tail => simp [List.append_assoc]
    · simp only [splitLoop, split, if_neg hc, ih, List.reverse_cons]
      cases hs : split separator rest with
      | nil => exact False.elim (split_nonempty separator rest hs)
      | cons first tail => simp [prependPart, List.append_assoc]

def splitSafe (separator : Char) (text : List Char) : List (List Char) :=
  splitLoop separator text [] []

theorem splitSafe_eq (separator : Char) (text : List Char) :
    splitSafe separator text = split separator text := by
  rw [splitSafe, splitLoop_reference]
  cases hs : split separator text with
  | nil => exact False.elim (split_nonempty separator text hs)
  | cons first rest => simp [prependPart]

def splitString (separator : Char) (text : String) : List String :=
  (splitSafe separator text.toList).map String.ofList

def joinString (separator : Char) (parts : List String) : String :=
  String.ofList (join separator (parts.map String.toList))

theorem splitString_joinString (separator : Char) (parts : List String)
    (nonempty : parts ≠ [])
    (clean : ∀ part ∈ parts, ∀ char ∈ part.toList, char ≠ separator) :
    splitString separator (joinString separator parts) = parts := by
  unfold splitString joinString
  rw [splitSafe_eq, String.toList_ofList]
  rw [split_join separator _ (by simpa using nonempty)]
  · simp only [List.map_map]
    have eq : String.ofList ∘ String.toList = id := by
      funext text
      simp only [Function.comp_apply, String.ofList_toList, id_eq]
    rw [eq, List.map_id]
  · intro part member
    obtain ⟨text, ht, rfl⟩ := List.mem_map.mp member
    exact clean text ht

theorem join_split (separator : Char) (text : List Char) :
    join separator (split separator text) = text := by
  induction text with
  | nil => rfl
  | cons char rest ih =>
    have nonempty := split_nonempty separator rest
    cases hs : split separator rest with
    | nil => exact False.elim (nonempty hs)
    | cons first tail =>
      rw [hs] at ih
      by_cases hc : char = separator
      · subst char
        simp only [split, hs, ite_true]
        change separator :: join separator (first :: tail) = separator :: rest
        exact congrArg (separator :: ·) ih
      · simp only [split, if_neg hc, hs]
        have hj : join separator ((char :: first) :: tail) =
            char :: join separator (first :: tail) := by cases tail <;> rfl
        rw [hj, ih]

theorem split_parts_clean (separator : Char) (text : List Char) :
    ∀ part ∈ split separator text, ∀ char ∈ part, char ≠ separator := by
  induction text with
  | nil => simp [split]
  | cons char rest ih =>
    by_cases hc : char = separator
    · subst char
      intro part member value inside
      simp only [split, ite_true, List.mem_cons] at member
      rcases member with rfl | member
      · simp at inside
      · exact ih part member value inside
    · cases hs : split separator rest with
      | nil => exact False.elim (split_nonempty separator rest hs)
      | cons first tail =>
        simp only [hs] at ih
        intro part member value inside
        simp only [split, if_neg hc, hs, List.mem_cons] at member
        rcases member with rfl | member
        · rcases List.mem_cons.mp inside with rfl | inside
          · exact hc
          · exact ih first (by simp) value inside
        · exact ih part (by simp [member]) value inside

theorem joinString_splitString (separator : Char) (text : String) :
    joinString separator (splitString separator text) = text := by
  unfold joinString splitString
  rw [splitSafe_eq]
  simp only [List.map_map]
  have eq : String.toList ∘ String.ofList = id := by
    funext chars
    simp only [Function.comp_apply, String.toList_ofList, id_eq]
  rw [eq, List.map_id, join_split, String.ofList_toList]

theorem splitString_parts_clean (separator : Char) (text : String) :
    ∀ part ∈ splitString separator text, ∀ char ∈ part.toList, char ≠ separator := by
  intro part member
  simp only [splitString, splitSafe_eq] at member
  obtain ⟨chars, hm, rfl⟩ := List.mem_map.mp member
  simpa only [String.toList_ofList] using split_parts_clean separator text.toList chars hm

theorem join_append (separator : Char) (left right : List (List Char))
    (hl : left ≠ []) (hr : right ≠ []) :
    join separator (left ++ right) = join separator left ++ separator :: join separator right := by
  induction left with
  | nil => contradiction
  | cons first rest ih =>
    cases rest with
    | nil => cases right <;> simp_all [join]
    | cons second rest =>
      simp only [List.cons_append, join]
      have hi := ih (by simp)
      simp only [List.cons_append] at hi
      rw [hi]
      simp only [List.append_assoc, List.cons_append]

theorem joinString_append (separator : Char) (left right : List String)
    (hl : left ≠ []) (hr : right ≠ []) :
    joinString separator (left ++ right) =
      joinString separator left ++ String.ofList [separator] ++ joinString separator right := by
  unfold joinString
  rw [List.map_append, join_append separator _ _ (by simpa using hl) (by simpa using hr)]
  rw [String.ofList_append]
  rw [String.append_assoc]
  congr 1
  exact @String.ofList_append [separator] _

theorem join_clean (separator forbidden : Char) (parts : List (List Char))
    (different : separator ≠ forbidden)
    (clean : ∀ part ∈ parts, ∀ char ∈ part, char ≠ forbidden) :
    ∀ char ∈ join separator parts, char ≠ forbidden := by
  induction parts with
  | nil => simp [join]
  | cons first rest ih =>
    cases rest with
    | nil => exact clean first (by simp)
    | cons second rest =>
      simp only [join, List.mem_append, List.mem_cons]
      intro char member
      rcases member with member | rfl | member
      · exact clean first (by simp) char member
      · exact different
      · apply ih (fun part member => clean part (by simp [member])) char member

theorem intercalate_head_prefix (before initial separator : String) (rest : List String) :
    String.intercalate separator ((before ++ initial) :: rest) =
      before ++ String.intercalate separator (initial :: rest) := by
  induction rest generalizing initial with
  | nil => rfl
  | cons next rest ih =>
    change String.intercalate separator ((before ++ initial ++ separator ++ next) :: rest) =
      before ++ String.intercalate separator ((initial ++ separator ++ next) :: rest)
    rw [show before ++ initial ++ separator ++ next = before ++ (initial ++ separator ++ next) by
      simp only [String.append_assoc]]
    exact ih _

theorem joinString_eq_intercalate (separator : Char) (parts : List String) :
    joinString separator parts = String.intercalate (String.ofList [separator]) parts := by
  induction parts with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => simp [joinString, join]; rfl
    | cons second rest =>
      unfold joinString at ih ⊢
      simp only [List.map_cons, join]
      rw [String.ofList_append]
      have hsep : String.ofList (separator :: join separator (List.map String.toList (second :: rest))) =
          String.ofList [separator] ++ String.ofList (join separator (List.map String.toList (second :: rest))) := by
        exact @String.ofList_append [separator] _
      rw [String.ofList_toList]
      change first ++ String.ofList (separator :: join separator (List.map String.toList (second :: rest))) = _
      rw [hsep, ih]
      rw [← String.append_assoc]
      change first ++ String.ofList [separator] ++ String.intercalate (String.ofList [separator]) (second :: rest) =
        String.intercalate (String.ofList [separator]) ((first ++ String.ofList [separator] ++ second) :: rest)
      rw [intercalate_head_prefix]

theorem splitString_append_separator (separator : Char) (first rest : String)
    (clean : ∀ char ∈ first.toList, char ≠ separator) :
    splitString separator (first ++ String.ofList [separator] ++ rest) =
      first :: splitString separator rest := by
  unfold splitString
  rw [splitSafe_eq, splitSafe_eq]
  simp only [String.toList_append, String.toList_ofList, List.append_assoc, List.singleton_append]
  rw [split_append_separator separator _ _ clean]
  simp only [List.map_cons, String.ofList_toList]

theorem splitString_joinPrefix (separator : Char) (fields : List String) (tail : String)
    (clean : ∀ field ∈ fields, ∀ char ∈ field.toList, char ≠ separator) :
    splitString separator (joinString separator (fields ++ [tail])) =
      fields ++ splitString separator tail := by
  induction fields with
  | nil => simp [joinString, join]
  | cons first rest ih =>
    have hjoin := joinString_append separator [first] (rest ++ [tail]) (by simp) (by simp)
    simp only [List.singleton_append] at hjoin
    simp only [List.cons_append]
    rw [hjoin]
    have hfirst : joinString separator [first] = first := by simp [joinString, join]
    rw [hfirst, splitString_append_separator separator _ _ (clean first (by simp))]
    rw [ih (fun field member => clean field (by simp [member]))]

end Tornado.Domain.CanonicalText


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

private def parseNoteLegacy (input : String) (chainId : ChainId) : Except String ParsedNote := do
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

/-- The canonical raw note has exactly five delimiter-separated fields. -/
def noteTextFields (pool : Pool) (preimage : String) : List String :=
  ["tornado", pool.asset.symbol.toLower, pool.denomination,
    toString (chainNumber pool.chainId), "0x" ++ preimage]

def renderNoteText (pool : Pool) (preimage : String) : String :=
  CanonicalText.joinString '-' (noteTextFields pool preimage)

/-- Lexical conditions are stated on fields, not as successful parsing. -/
def CanonicalNoteGrammar (pool : Pool) (preimage : String) : Prop :=
  (∀ field ∈ noteTextFields pool preimage, ∀ char ∈ field.toList, char ≠ '-') ∧
  (∀ field ∈ noteTextFields pool preimage, ∀ char ∈ field.toList, char ≠ '\n') ∧
  nonemptyAll pool.asset.symbol.toLower asciiAlphaNum = true ∧
  nonemptyAll pool.denomination (fun c => asciiDigit c || c == '.') = true ∧
  preimage.length = 124 ∧ preimage.toList.all asciiHex = true ∧
  preimage.toLower = preimage ∧
  poolFor pool.chainId pool.denomination pool.asset.symbol.toLower = some pool

/-- Whole-input canonical reader. Legacy whitespace and token extraction
remain available through the unchanged fallback below. -/
def parseCanonicalNote (raw : String) (chainId : ChainId) : Except String ParsedNote := do
  let [tag, symbol, denomination, chainText, secret] := CanonicalText.splitString '-' raw
    | throw "This is not a canonical withdrawal note."
  if tag != "tornado" || !nonemptyAll symbol asciiAlphaNum ||
      !nonemptyAll denomination (fun c => asciiDigit c || c == '.') ||
      !(chainText == "1" || chainText == "11155111") ||
      secret.toList.take 2 != "0x".toList || secret.length != 126 ||
      !(secret.toList.drop 2).all asciiHex then
    throw "This is not a canonical withdrawal note."
  if chainText != toString (chainNumber chainId) then
    throw "This note belongs to a different network."
  let some pool := poolFor chainId denomination symbol
    | throw "This note uses an unavailable denomination."
  return { raw, pool, preimage := String.ofList (secret.toList.drop 2) |>.toLower }

def parseNote (input : String) (chainId : ChainId) : Except String ParsedNote :=
  match parseCanonicalNote input chainId with
  | .ok note => .ok note
  | .error _ => parseNoteLegacy input chainId

theorem renderNoteText_legacy (pool : Pool) (preimage : String) :
    renderNoteText pool preimage =
      s!"tornado-{pool.asset.symbol.toLower}-{pool.denomination}-{chainNumber pool.chainId}-0x{preimage}" := by
  rw [renderNoteText, CanonicalText.joinString_eq_intercalate]
  have hdash : String.ofList ['-'] = "-" := by decide
  rw [hdash]
  simp only [noteTextFields, String.intercalate]
  change ("tornado" ++ "-" ++ pool.asset.symbol.toLower ++ "-" ++ pool.denomination ++ "-" ++
    toString (chainNumber pool.chainId) ++ "-" ++ ("0x" ++ preimage)) = _
  rw [show "tornado-" = "tornado" ++ "-" by decide, show "-0x" = "-" ++ "0x" by decide]
  simp only [String.append_assoc]
  rfl

theorem parseCanonicalNote_render (pool : Pool) (preimage : String)
    (grammar : CanonicalNoteGrammar pool preimage) :
    parseCanonicalNote (renderNoteText pool preimage) pool.chainId =
      .ok ⟨renderNoteText pool preimage, preimage, pool⟩ := by
  rcases grammar with ⟨dash, _, symbol, denomination, length, hex, lower, catalog⟩
  have fields := CanonicalText.splitString_joinString '-' (noteTextFields pool preimage)
    (by simp [noteTextFields]) dash
  have hprefix : ("0x" ++ preimage).toList.take 2 = "0x".toList := by
    simp [String.toList_append]
  have hlength : ("0x" ++ preimage).length = 126 := by simp [length, show "0x".length = 2 by decide]
  have hdrop : ("0x" ++ preimage).toList.drop 2 = preimage.toList := by
    simp [String.toList_append]
  have fields' : CanonicalText.splitString '-' (renderNoteText pool preimage) =
      ["tornado", pool.asset.symbol.toLower, pool.denomination,
        toString (chainNumber pool.chainId), "0x" ++ preimage] := fields
  simp only [parseCanonicalNote, fields']
  have hchain : (toString (chainNumber pool.chainId) == "1" ||
      toString (chainNumber pool.chainId) == "11155111") = true := by
    cases pool.chainId <;> decide
  simp only [Bool.or_eq_true, beq_iff_eq] at hchain
  rcases hchain with hchain | hchain <;>
    simp [symbol, denomination, hlength, hex, catalog, lower, hchain, pure, Except.pure, bind, Except.bind]

theorem renderNoteText_clean (pool : Pool) (preimage : String)
    (grammar : CanonicalNoteGrammar pool preimage) :
    ∀ char ∈ (renderNoteText pool preimage).toList, char ≠ '\n' := by
  unfold renderNoteText CanonicalText.joinString
  rw [String.toList_ofList]
  apply CanonicalText.join_clean '-' '\n' _ (by decide)
  intro part member
  obtain ⟨field, hm, rfl⟩ := List.mem_map.mp member
  exact grammar.2.1 field hm

theorem parseNote_render (pool : Pool) (preimage : String)
    (grammar : CanonicalNoteGrammar pool preimage) :
    parseNote (renderNoteText pool preimage) pool.chainId =
      .ok ⟨renderNoteText pool preimage, preimage, pool⟩ := by
  simp only [parseNote, parseCanonicalNote_render pool preimage grammar]

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

def poolTextFields (pool : Pool) : List String :=
  ["tornado", pool.asset.symbol.toLower, pool.denomination,
    toString (chainNumber pool.chainId), "0x"]

def CanonicalPoolGrammar (pool : Pool) : Prop :=
  (∀ field ∈ poolTextFields pool, ∀ char ∈ field.toList, char ≠ '-' ∧ char ≠ '\n') ∧
  nonemptyAll pool.asset.symbol.toLower asciiAlphaNum = true ∧
  nonemptyAll pool.denomination (fun c => asciiDigit c || c == '.') = true ∧
  poolFor pool.chainId pool.denomination pool.asset.symbol.toLower = some pool

theorem toLower_chars (text : String) :
    text.toLower = String.ofList (text.toList.map Char.toLower) := by
  apply String.toList_inj.mp
  simp only [String.toLower, String.toList_map, String.toList_ofList]

set_option linter.unusedSimpArgs false in
theorem catalog_pool_grammar (pool : Pool) (inside : pool ∈ allPools) : CanonicalPoolGrammar pool := by
  have facts : poolFor pool.chainId pool.denomination pool.asset.symbol.toLower = some pool ∧
      (poolTextFields pool).all (fun field => field.toList.all (fun char => char != '-' && char != '\n')) = true ∧
      nonemptyAll pool.asset.symbol.toLower asciiAlphaNum = true ∧
      nonemptyAll pool.denomination (fun c => asciiDigit c || c == '.') = true := by
    simp only [allPools, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same | same
    all_goals subst pool
    all_goals refine ⟨?_, ?_, ?_, ?_⟩
    all_goals first
      | (simp only [poolFor, poolsFor, allPools, toLower_chars]; rfl)
      | (simp only [poolTextFields, nonemptyAll, toLower_chars]; decide)
  rcases facts with ⟨known, clean, symbol, denomination⟩
  refine ⟨?_, symbol, denomination, known⟩
  intro field member char present
  have actual := List.all_eq_true.mp (List.all_eq_true.mp clean field member) char present
  simpa using actual

theorem canonicalNoteGrammar_hex (pool : Pool) (preimage : String)
    (supported : pool ∈ allPools) (length : preimage.length = 124)
    (lexical : preimage.toList.all LeanCrypto.Hex.lowerHex = true)
    (lower : preimage.toLower = preimage) : CanonicalNoteGrammar pool preimage := by
  obtain ⟨poolClean, symbol, denomination, known⟩ := catalog_pool_grammar pool supported
  have chars : ∀ char ∈ preimage.toList, char ≠ '-' ∧ char ≠ '\n' := by
    intro char member
    have actual := List.all_eq_true.mp lexical char member
    constructor
    · intro same; subst char; change false = true at actual; contradiction
    · intro same; subst char; change false = true at actual; contradiction
  have clean : ∀ field ∈ noteTextFields pool preimage, ∀ char ∈ field.toList,
      char ≠ '-' ∧ char ≠ '\n' := by
    intro field member char present
    simp only [noteTextFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact poolClean _ (by simp [poolTextFields]) char present
    · exact poolClean _ (by simp [poolTextFields]) char present
    · exact poolClean _ (by simp [poolTextFields]) char present
    · exact poolClean _ (by simp [poolTextFields]) char present
    · rw [String.toList_append] at present
      rcases List.mem_append.mp present with prefixMember | secretMember
      · exact poolClean "0x" (by simp [poolTextFields]) char prefixMember
      · exact chars char secretMember
  have hex : preimage.toList.all asciiHex = true := by
    apply List.all_eq_true.mpr
    intro char member
    have actual := List.all_eq_true.mp lexical char member
    simp only [LeanCrypto.Hex.lowerHex, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at actual
    rcases actual with digit | letter
    · simp [asciiHex, asciiDigit, digit.1, digit.2]
    · simp [asciiHex, letter.1, letter.2]
  exact ⟨fun field member char present => (clean field member char present).1,
    fun field member char present => (clean field member char present).2,
    symbol, denomination, length, hex, lower, known⟩

end Tornado.Domain

#print axioms Tornado.Domain.CanonicalText.split_nonempty
#print axioms Tornado.Domain.CanonicalText.split_append_separator
#print axioms Tornado.Domain.CanonicalText.split_clean
#print axioms Tornado.Domain.CanonicalText.split_join
#print axioms Tornado.Domain.CanonicalText.splitString_joinString
#print axioms Tornado.Domain.CanonicalText.intercalate_head_prefix
#print axioms Tornado.Domain.CanonicalText.joinString_eq_intercalate
#print axioms Tornado.Domain.renderNoteText_legacy
#print axioms Tornado.Domain.parseCanonicalNote_render
#print axioms Tornado.Domain.parseNote_render

#print axioms Tornado.Domain.CanonicalText.join_split
#print axioms Tornado.Domain.CanonicalText.split_parts_clean
#print axioms Tornado.Domain.CanonicalText.joinString_splitString
#print axioms Tornado.Domain.CanonicalText.splitString_parts_clean

#print axioms Tornado.Domain.CanonicalText.join_append
#print axioms Tornado.Domain.CanonicalText.joinString_append
#print axioms Tornado.Domain.CanonicalText.join_clean
#print axioms Tornado.Domain.renderNoteText_clean

#print axioms Tornado.Domain.CanonicalText.splitLoop_reference
#print axioms Tornado.Domain.CanonicalText.splitSafe_eq

#print axioms Tornado.Domain.CanonicalText.splitString_append_separator
#print axioms Tornado.Domain.CanonicalText.splitString_joinPrefix

#print axioms Tornado.Domain.catalog_pool_grammar
#print axioms Tornado.Domain.canonicalNoteGrammar_hex

#print axioms Tornado.Domain.toLower_chars
