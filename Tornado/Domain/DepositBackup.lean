import Tornado.Domain.Invoice
import Tornado.Domain.NoteCreation

/-!
Pure parsing of a private backup into public deposit identities. The input may
contain secret notes and a seed phrase; callers must never print it or include
it in errors. This matches the pinned CLI's note-like token extraction,
same-asset rule and duplicate-nullifier guard for inspect/invoice commands.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace Tornado.Domain

structure BackupIdentity where
  note : ParsedNote
  publicIdentity : NoteIdentity
  -- The nested note is spendable; keep it out of generic debug formatting.
  deriving BEq, Inhabited

/-- Canonical line reader consumes every line, including the final newline. -/
def parseCanonicalBackupLines (chain : ChainId) : List String → Except String (List ParsedNote)
  | [] => .error "Canonical note backup must end with a newline."
  | raw :: rest =>
      if rest.isEmpty && raw == "" then .ok []
      else do
        let note ← parseCanonicalNote raw chain
        let notes ← parseCanonicalBackupLines chain rest
        return note :: notes

def seedPhraseGrammar (phrase : String) : Bool :=
  !phrase.isEmpty && phrase.toList.all (fun char =>
    ('a' ≤ char && char ≤ 'z') || char == ' ')

def readSeedBlock : List String → List String → Except String (List String × List String)
  | [], _ => .error "Missing canonical note block terminator."
  | line :: rest, collected =>
      if line = seedNoteFooter then .ok (collected.reverse, rest)
      else readSeedBlock rest (line :: collected)

def parseCanonicalSeedLines (lines : List String) (chain : ChainId) : Except String (List ParsedNote) := do
  let header :: phrase :: divider :: blank :: noteHeader :: rest := lines
    | throw "This is not a canonical seeded backup."
  if header != "------- SEED PHRASE (SECRET) --------" ||
      divider != "-------------------------------------" || blank != "" ||
      noteHeader != "-------- NOTES (SECRET) --------" || !seedPhraseGrammar phrase then
    throw "This is not a canonical seeded backup."
  let (notes, tail) ← readSeedBlock rest []
  if notes.length > 100 then throw "Canonical backup contains too many notes."
  if CanonicalText.joinString '\n' tail != seedTailText (seedNonceText ((List.range notes.length).map some)) then
    throw "Canonical seed metadata does not describe contiguous note nonces."
  parseCanonicalBackupLines chain (notes ++ [""])

def parseCanonicalBackupText (input : String) (chain : ChainId) : Except String (List ParsedNote) :=
  let lines := CanonicalText.splitString '\n' input
  let plain := if lines.length ≤ 101 then parseCanonicalBackupLines chain lines
    else .error "Canonical backup contains too many lines."
  match plain with
  | .ok notes => .ok notes
  | .error _ => parseCanonicalSeedLines lines chain

def parseBackupNotes (input : String) (chain : ChainId) : Except String (List ParsedNote) :=
  match parseCanonicalBackupText input chain with
  | .ok notes => .ok notes
  | .error _ => do
      let raw ← extractNoteStrings input
      raw.mapM (parseNote · chain)

theorem readSeedBlock_construct (notes tail collected : List String)
    (ordinary : ∀ raw ∈ notes, raw ≠ seedNoteFooter) :
    readSeedBlock (notes ++ seedNoteFooter :: tail) collected =
      .ok (collected.reverse ++ notes, tail) := by
  induction notes generalizing collected with
  | nil => simp [readSeedBlock]
  | cons first rest ih =>
    simp only [List.cons_append, readSeedBlock, if_neg (ordinary first (by simp))]
    rw [ih _ (fun raw member => ordinary raw (by simp [member]))]
    simp [List.reverse_cons, List.append_assoc]

theorem seedPhrase_clean (phrase : String) (grammar : seedPhraseGrammar phrase = true) :
    '\n' ∉ phrase.toList := by
  intro member
  have both := grammar
  unfold seedPhraseGrammar at both
  simp only [Bool.and_eq_true] at both
  have all := both.2
  have actual := List.all_eq_true.mp all '\n' member
  have impossible : ((('a' ≤ '\n') && ('\n' ≤ 'z')) || ('\n' == ' ')) = false := by decide
  rw [impossible] at actual
  contradiction

theorem seededBackupText_split (source : List CreatedNote) (phrase : String)
    (phraseGrammar : seedPhraseGrammar phrase = true)
    (grammar : ∀ note ∈ source, CanonicalNoteGrammar note.pool note.preimage)
    (rendered : ∀ note ∈ source, note.raw = renderNoteText note.pool note.preimage) :
    CanonicalText.splitString '\n' (seededBackupText source phrase) =
      seedHeaderLines phrase ++ source.map CreatedNote.raw ++ seedNoteFooter ::
        CanonicalText.splitString '\n' (seedTailText (seedNonceText (source.map CreatedNote.nonce))) := by
  unfold seededBackupText
  rw [show seedHeaderLines phrase ++ source.map CreatedNote.raw ++
      [seedNoteFooter, seedTailText (seedNonceText (source.map CreatedNote.nonce))] =
      (seedHeaderLines phrase ++ source.map CreatedNote.raw ++ [seedNoteFooter]) ++
        [seedTailText (seedNonceText (source.map CreatedNote.nonce))] by simp [List.append_assoc]]
  rw [CanonicalText.splitString_joinPrefix]
  · simp [List.append_assoc]
  · intro field member char inside equal
    subst char
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · simp only [seedHeaderLines, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl
        · exact (by decide : '\n' ∉ "------- SEED PHRASE (SECRET) --------".toList) inside
        · exact seedPhrase_clean _ phraseGrammar inside
        · exact (by decide : '\n' ∉ "-------------------------------------".toList) inside
        · simp at inside
        · exact (by decide : '\n' ∉ "-------- NOTES (SECRET) --------".toList) inside
      · obtain ⟨note, hm, rfl⟩ := List.mem_map.mp member
        rw [rendered note hm] at inside
        exact renderNoteText_clean note.pool note.preimage (grammar note hm) '\n' inside rfl
    · simp only [List.mem_singleton] at member
      subst field
      exact (by decide : '\n' ∉ seedNoteFooter.toList) inside


/-- Both readers share the original same-asset, reused-nullifier and public
Pedersen-identity checks. No seed or note text is placed in errors. -/
def identifyBackupNotes (notes : List ParsedNote) : Except String (List BackupIdentity) := do
  let some first := notes.head? | throw "No Tornado note strings were found in this file."
  if notes.any (fun note => note.pool.asset.symbol != first.pool.asset.symbol) then
    throw "Use notes of one asset per deposit session."
  let nullifiers := notes.map fun note => String.ofList (note.preimage.toList.take 62)
  if nullifiers.eraseDups.length != notes.length then
    throw "The backup contains duplicate notes or reused nullifiers."
  notes.mapM fun note => do
    return { note, publicIdentity := (← noteIdentity note) }

def parseDepositBackup (input : String) (chainId : ChainId) :
    Except String (List BackupIdentity) := do
  let notes ← parseBackupNotes input chainId
  identifyBackupNotes notes

/-- Generic Except-list construction from pointwise primitive success. -/
theorem mapM_construct (source : List α) (run : α → Except String β) (value : α → β)
    (success : ∀ input ∈ source, run input = .ok (value input)) :
    source.mapM run = .ok (source.map value) := by
  induction source with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.mapM_cons, success first (by simp), List.map_cons]
    rw [ih (fun input member => success input (by simp [member]))]
    rfl

theorem mapM_provenance (source : List α) (run : α → Except String β) (output : List β)
    (success : source.mapM run = .ok output) :
    ∀ value ∈ output, ∃ input ∈ source, run input = .ok value := by
  induction source generalizing output with
  | nil => simp [List.mapM_nil, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at success; subst output; simp
  | cons first rest ih =>
    simp only [List.mapM_cons] at success
    cases head : run first with
    | error message => simp [head, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at success
    | ok value =>
      cases tail : rest.mapM run with
      | error message => simp [head, tail, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at success
      | ok values =>
        simp [head, tail, bind, Except.bind, pure, Except.pure, Functor.map, Except.map] at success
        subst output
        intro actual member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨first, by simp, head⟩
        · obtain ⟨input, member, bound⟩ := ih values tail actual member
          exact ⟨input, by simp [member], bound⟩

def createdParsed (note : CreatedNote) : ParsedNote := ⟨note.raw, note.preimage, note.pool⟩

theorem parseCanonicalBackupLines_construct (source : List CreatedNote) (chain : ChainId)
    (grammar : ∀ note ∈ source, CanonicalNoteGrammar note.pool note.preimage)
    (rendered : ∀ note ∈ source, note.raw = renderNoteText note.pool note.preimage)
    (network : ∀ note ∈ source, note.pool.chainId = chain) :
    parseCanonicalBackupLines chain (source.map CreatedNote.raw ++ [""]) =
      .ok (source.map createdParsed) := by
  induction source with
  | nil => rfl
  | cons first rest ih =>
    have firstParsed : parseCanonicalNote first.raw chain = .ok (createdParsed first) := by
      rw [← network first (by simp), rendered first (by simp)]
      simpa only [createdParsed, rendered first (by simp)] using
        parseCanonicalNote_render first.pool first.preimage (grammar first (by simp))
    have tailNotEmpty : (rest.map (·.raw) ++ [""]).isEmpty = false := by cases rest <;> rfl
    simp only [List.map_cons, List.cons_append, parseCanonicalBackupLines, tailNotEmpty,
      List.isEmpty_cons, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [firstParsed]
    rw [ih (fun note member => grammar note (by simp [member]))
      (fun note member => rendered note (by simp [member]))
      (fun note member => network note (by simp [member]))]
    rfl

theorem parseBackupNotes_plain_construct (source : List CreatedNote) (chain : ChainId)
    (nonempty : source ≠ []) (limit : source.length ≤ 100)
    (grammar : ∀ note ∈ source, CanonicalNoteGrammar note.pool note.preimage)
    (rendered : ∀ note ∈ source, note.raw = renderNoteText note.pool note.preimage)
    (network : ∀ note ∈ source, note.pool.chainId = chain) :
    parseBackupNotes (rawBackup source) chain = .ok (source.map createdParsed) := by
  rw [rawBackup_canonical source nonempty]
  have clean : ∀ line ∈ source.map CreatedNote.raw ++ [""], ∀ char ∈ line.toList, char ≠ '\n' := by
    intro line member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨note, hm, rfl⟩ := List.mem_map.mp member
      rw [rendered note hm]
      exact renderNoteText_clean note.pool note.preimage (grammar note hm)
    · simp only [List.mem_singleton] at member
      subst line
      simp
  unfold parseBackupNotes parseCanonicalBackupText
  rw [CanonicalText.splitString_joinString '\n' _ (by simp) clean]
  dsimp only
  rw [if_pos (by simpa using Nat.add_le_add_right limit 1)]
  rw [parseCanonicalBackupLines_construct source chain grammar rendered network]

theorem parseBackupNotes_seeded_construct (source : List CreatedNote) (chain : ChainId)
    (phrase : String) (limit : source.length ≤ 100)
    (phraseGrammar : seedPhraseGrammar phrase = true)
    (grammar : ∀ note ∈ source, CanonicalNoteGrammar note.pool note.preimage)
    (rendered : ∀ note ∈ source, note.raw = renderNoteText note.pool note.preimage)
    (network : ∀ note ∈ source, note.pool.chainId = chain)
    (nonces : source.map CreatedNote.nonce = (List.range source.length).map some) :
    parseBackupNotes (seededBackupText source phrase) chain = .ok (source.map createdParsed) := by
  have ordinary : ∀ raw ∈ source.map CreatedNote.raw, raw ≠ seedNoteFooter := by
    intro raw member equal
    obtain ⟨note, hm, rfl⟩ := List.mem_map.mp member
    have parsed := parseCanonicalNote_render note.pool note.preimage (grammar note hm)
    rw [← rendered note hm, equal] at parsed
    have impossible : parseCanonicalNote seedNoteFooter note.pool.chainId =
        .error "This is not a canonical withdrawal note." := by rfl
    rw [impossible] at parsed
    contradiction
  unfold parseBackupNotes parseCanonicalBackupText
  rw [seededBackupText_split source phrase phraseGrammar grammar rendered]
  dsimp only
  generalize tailDefinition : CanonicalText.splitString '\n' (seedTailText (seedNonceText (source.map CreatedNote.nonce))) = tail
  have tailMatches : CanonicalText.joinString '\n' tail =
      seedTailText (seedNonceText (source.map CreatedNote.nonce)) := by
    rw [← tailDefinition, CanonicalText.joinString_splitString]
  have headerRejected : parseCanonicalNote "------- SEED PHRASE (SECRET) --------" chain =
      .error "This is not a canonical withdrawal note." := by rfl
  have canonical : parseCanonicalSeedLines (seedHeaderLines phrase ++ source.map CreatedNote.raw ++
      seedNoteFooter :: tail) chain = .ok (source.map createdParsed) := by
    simp only [seedHeaderLines, List.cons_append, parseCanonicalSeedLines]
    simp only [bne_self_eq_false, Bool.false_or, phraseGrammar, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    simp only [List.nil_append]
    rw [readSeedBlock_construct _ _ [] ordinary]
    simp only [List.reverse_nil, List.nil_append]
    rw [if_neg (show ¬ (source.map CreatedNote.raw).length > 100 by simpa using Nat.not_lt_of_ge limit)]
    rw [tailMatches, List.length_map, nonces]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind]
    exact parseCanonicalBackupLines_construct source chain grammar rendered network
  have plainRejected : parseCanonicalBackupLines chain (seedHeaderLines phrase ++ source.map CreatedNote.raw ++
      seedNoteFooter :: tail) =
        .error "This is not a canonical withdrawal note." := by
    change (do
      let note ← parseCanonicalNote "------- SEED PHRASE (SECRET) --------" chain
      let notes ← parseCanonicalBackupLines chain (phrase :: "-------------------------------------" :: "" ::
        "-------- NOTES (SECRET) --------" :: (source.map CreatedNote.raw ++ seedNoteFooter ::
          tail))
      return note :: notes) = .error "This is not a canonical withdrawal note."
    rw [headerRejected]
    rfl
  by_cases lengthBound : (seedHeaderLines phrase ++ source.map CreatedNote.raw ++ seedNoteFooter ::
      tail).length ≤ 101
  · simp only [if_pos lengthBound, plainRejected, canonical]
  · simp only [if_neg lengthBound, canonical]

/-- Construction uses grammar, catalog/network, same-asset and distinct
nullifier conditions plus explicit success of the native public hash primitive.
It does not assume success of either backup reader or of the final validator. -/
theorem identifyBackupNotes_construct (source : List CreatedNote)
    (identities : CreatedNote → NoteIdentity) (nonempty : source ≠ [])
    (sameAsset : ∀ first ∈ source, ∀ note ∈ source,
      note.pool.asset.symbol = first.pool.asset.symbol)
    (distinct : (source.map (fun note => String.ofList (note.preimage.toList.take 62))).eraseDups.length = source.length)
    (identity : ∀ note ∈ source, noteIdentity (createdParsed note) = .ok (identities note)) :
    identifyBackupNotes (source.map createdParsed) = .ok (source.map (fun note =>
      ({ note := createdParsed note, publicIdentity := identities note } : BackupIdentity))) := by
  cases source with
  | nil => contradiction
  | cons first rest =>
    have sameFalse : ((first :: rest).map createdParsed).any
        (fun note => note.pool.asset.symbol != first.pool.asset.symbol) = false := by
      apply List.any_eq_false.mpr
      intro parsed member
      obtain ⟨note, hm, rfl⟩ := List.mem_map.mp member
      simp [createdParsed, sameAsset first (by simp) note hm]
    have mapped := mapM_construct (first :: rest)
      (fun note => do
        let publicIdentity ← noteIdentity (createdParsed note)
        return ({ note := createdParsed note, publicIdentity } : BackupIdentity))
      (fun note => ({ note := createdParsed note, publicIdentity := identities note } : BackupIdentity))
      (by intro note member; simp [identity note member, bind, Except.bind, pure, Except.pure])
    have assetNo : ¬ ∃ note, note ∈ rest ∧ note.pool.asset.symbol ≠ first.pool.asset.symbol := by
      rintro ⟨note, member, different⟩
      exact different (sameAsset first (by simp) note (by simp [member]))
    simp only [List.map_cons] at sameFalse
    simp only [List.map_cons, List.length_cons] at distinct
    simpa [identifyBackupNotes, sameFalse, distinct, List.mapM_map, createdParsed,
      Function.comp_def, bind, Except.bind, pure, Except.pure, List.map_map, assetNo] using mapped

theorem parseDepositBackup_plain_construct (source : List CreatedNote) (chain : ChainId)
    (identities : CreatedNote → NoteIdentity) (nonempty : source ≠ []) (limit : source.length ≤ 100)
    (grammar : ∀ note ∈ source, CanonicalNoteGrammar note.pool note.preimage)
    (rendered : ∀ note ∈ source, note.raw = renderNoteText note.pool note.preimage)
    (network : ∀ note ∈ source, note.pool.chainId = chain)
    (sameAsset : ∀ first ∈ source, ∀ note ∈ source,
      note.pool.asset.symbol = first.pool.asset.symbol)
    (distinct : (source.map (fun note => String.ofList (note.preimage.toList.take 62))).eraseDups.length = source.length)
    (identity : ∀ note ∈ source, noteIdentity (createdParsed note) = .ok (identities note)) :
    ∃ backup,
      formatDepositBackup source none = .ok backup ∧
      parseDepositBackup backup chain = .ok (source.map (fun note =>
        ({ note := createdParsed note, publicIdentity := identities note } : BackupIdentity))) := by
  refine ⟨rawBackup source, rfl, ?_⟩
  unfold parseDepositBackup
  rw [parseBackupNotes_plain_construct source chain nonempty limit grammar rendered network]
  exact identifyBackupNotes_construct source identities nonempty sameAsset distinct identity

/-- Public identifiers in every successful parse were recomputed by the
actual native identity function, never copied from supplied backup metadata. -/
theorem identifyBackupNotes_provenance (notes : List ParsedNote) (entries : List BackupIdentity)
    (success : identifyBackupNotes notes = .ok entries) :
    ∀ entry ∈ entries, entry.note ∈ notes ∧ noteIdentity entry.note = .ok entry.publicIdentity := by
  cases notes with
  | nil => simp [identifyBackupNotes, bind, Except.bind] at success
  | cons first rest =>
    by_cases same : (first :: rest).any (fun note => note.pool.asset.symbol != first.pool.asset.symbol) = true
    · simp [identifyBackupNotes, same, bind, Except.bind] at success
    · by_cases unique : ((first :: rest).map (fun note => String.ofList (note.preimage.toList.take 62))).eraseDups.length =
          (first :: rest).length
      · simp only [List.map_cons, List.length_cons] at unique
        have mapped : (first :: rest).mapM (fun note => do
            return ({ note, publicIdentity := (← noteIdentity note) } : BackupIdentity)) = .ok entries := by
          simpa [identifyBackupNotes, same, unique, bind, Except.bind, pure, Except.pure] using success
        intro entry member
        obtain ⟨note, hm, identity⟩ := mapM_provenance (first :: rest) _ entries mapped entry member
        cases result : noteIdentity note with
        | error message => simp [result, bind, Except.bind] at identity
        | ok publicIdentity =>
          simp [result, bind, Except.bind, pure, Except.pure] at identity
          subst entry
          exact ⟨hm, result⟩
      · simp only [List.map_cons, List.length_cons] at unique
        simp [identifyBackupNotes, same, unique, bind, Except.bind, pure, Except.pure] at success

theorem parseDepositBackup_provenance (input : String) (chain : ChainId)
    (entries : List BackupIdentity) (success : parseDepositBackup input chain = .ok entries) :
    ∃ notes, parseBackupNotes input chain = .ok notes ∧
      ∀ entry ∈ entries, entry.note ∈ notes ∧ noteIdentity entry.note = .ok entry.publicIdentity := by
  cases parsed : parseBackupNotes input chain with
  | error message => simp [parseDepositBackup, parsed, bind, Except.bind] at success
  | ok notes =>
    have identified : identifyBackupNotes notes = .ok entries := by
      simpa [parseDepositBackup, parsed, bind, Except.bind] using success
    exact ⟨notes, rfl, identifyBackupNotes_provenance notes entries identified⟩

end Tornado.Domain

#print axioms Tornado.Domain.mapM_construct
#print axioms Tornado.Domain.mapM_provenance
#print axioms Tornado.Domain.parseCanonicalBackupLines_construct
#print axioms Tornado.Domain.parseBackupNotes_plain_construct
#print axioms Tornado.Domain.identifyBackupNotes_provenance
#print axioms Tornado.Domain.parseDepositBackup_provenance

#print axioms Tornado.Domain.identifyBackupNotes_construct
#print axioms Tornado.Domain.parseDepositBackup_plain_construct

#print axioms Tornado.Domain.readSeedBlock_construct
#print axioms Tornado.Domain.seedPhrase_clean
#print axioms Tornado.Domain.seededBackupText_split
#print axioms Tornado.Domain.parseBackupNotes_seeded_construct
