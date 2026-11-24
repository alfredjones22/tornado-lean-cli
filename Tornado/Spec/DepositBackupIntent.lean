import Tornado.Cli.DepositMulti

/-! Original private-note backup provenance, separate from public invoices.
Construction conditions describe source grammar, catalog/network/asset and
nullifier distinctness. Native public hash and commitment-hex success remain
explicit primitive obligations; successful final parsing is not a premise. -/
set_option linter.unusedSimpArgs false
namespace Tornado.Spec.DepositBackupIntent

open Tornado.Domain Tornado.Cli

private def publicItemsLoop (entries : List BackupIdentity) (initial : Array DepositMulti.Item) :
    Except String (Array DepositMulti.Item) := do
  let mut items := initial
  for entry in entries do
    let commitment ← parseHexBytes entry.publicIdentity.commitment
    if commitment.size != 32 then throw "Generated note commitment is not bytes32."
    items := items.push ⟨entry.note.pool, commitment⟩
  return items

theorem publicItemsLoop_construct (entries : List BackupIdentity)
    (commitments : BackupIdentity → ByteArray)
    (decoded : ∀ entry ∈ entries, parseHexBytes entry.publicIdentity.commitment = .ok (commitments entry))
    (width : ∀ entry ∈ entries, (commitments entry).size = 32)
    (initial : Array DepositMulti.Item) :
    publicItemsLoop entries initial = .ok (initial ++ (entries.map (fun entry =>
      (⟨entry.note.pool, commitments entry⟩ : DepositMulti.Item))).toArray) := by
  induction entries generalizing initial with
  | nil => simp [publicItemsLoop, pure, Except.pure, bind, Except.bind]
  | cons first rest ih =>
    simp only [publicItemsLoop, List.forIn_cons, decoded first (by simp),
      width first (by simp), bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    simp only [bind, Except.bind, pure, Except.pure, width first (by simp), bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    change publicItemsLoop rest (initial.push ⟨first.note.pool, commitments first⟩) = _
    rw [ih (fun entry member => decoded entry (by simp [member]))
      (fun entry member => width entry (by simp [member]))]
    congr 1
    apply Array.toList_inj.mp
    simp [Array.toList_append]

/-- Exact projection for the actual CLI function, including its cheap count
check before public-identity hashing. -/
theorem publicItems_of_backup (raw : String) (chain : ChainId)
    (notes : List ParsedNote) (entries : List BackupIdentity)
    (parsedNotes : parseBackupNotes raw chain = .ok notes) (limit : notes.length ≤ 100)
    (parsed : parseDepositBackup raw chain = .ok entries)
    (commitments : BackupIdentity → ByteArray)
    (decoded : ∀ entry ∈ entries, parseHexBytes entry.publicIdentity.commitment = .ok (commitments entry))
    (width : ∀ entry ∈ entries, (commitments entry).size = 32) :
    DepositMulti.publicItems raw chain = .ok ((entries.map (fun entry =>
      (⟨entry.note.pool, commitments entry⟩ : DepositMulti.Item))).toArray) := by
  unfold DepositMulti.publicItems
  rw [parsedNotes]
  simp only [bind, Except.bind]
  rw [if_neg (show ¬ notes.length > 100 by omega)]
  simp only [pure, Except.pure, bind, Except.bind]
  rw [parsed]
  change publicItemsLoop entries #[] = _
  simpa only [Array.empty_append] using publicItemsLoop_construct entries commitments decoded width #[]

structure Source (chain : ChainId) where
  notes : List CreatedNote
  identities : CreatedNote → NoteIdentity
  commitments : BackupIdentity → ByteArray
  nonempty : notes ≠ []
  limit : notes.length ≤ 100
  grammar : ∀ note ∈ notes, CanonicalNoteGrammar note.pool note.preimage
  rendered : ∀ note ∈ notes, note.raw = renderNoteText note.pool note.preimage
  network : ∀ note ∈ notes, note.pool.chainId = chain
  sameAsset : ∀ first ∈ notes, ∀ note ∈ notes,
    note.pool.asset.symbol = first.pool.asset.symbol
  distinct : (notes.map (fun note => String.ofList (note.preimage.toList.take 62))).eraseDups.length = notes.length
  identity : ∀ note ∈ notes, noteIdentity (createdParsed note) = .ok (identities note)
  decoded : ∀ note ∈ notes,
    let entry : BackupIdentity := ⟨createdParsed note, identities note⟩
    parseHexBytes entry.publicIdentity.commitment = .ok (commitments entry)
  width : ∀ note ∈ notes,
    let entry : BackupIdentity := ⟨createdParsed note, identities note⟩
    (commitments entry).size = 32

def Source.entries (source : Source chain) : List BackupIdentity :=
  source.notes.map (fun note => ⟨createdParsed note, source.identities note⟩)

def Source.items (source : Source chain) : Array DepositMulti.Item :=
  (source.entries.map (fun entry => ⟨entry.note.pool, source.commitments entry⟩)).toArray

/-- Actual formatter → actual parser → actual publicItems construction.
No successful final guard is supplied by the caller. -/
theorem source_construct (source : Source chain) :
    ∃ raw, formatDepositBackup source.notes none = .ok raw ∧
      parseDepositBackup raw chain = .ok source.entries ∧
      DepositMulti.publicItems raw chain = .ok source.items := by
  obtain ⟨raw, formatted, parsed⟩ := parseDepositBackup_plain_construct source.notes chain
    source.identities source.nonempty source.limit source.grammar source.rendered source.network
    source.sameAsset source.distinct source.identity
  have exactRaw : raw = rawBackup source.notes := by
    simpa only [formatDepositBackup, pure, Except.pure, Except.ok.injEq] using formatted.symm
  subst raw
  refine ⟨rawBackup source.notes, formatted, parsed, ?_⟩
  apply publicItems_of_backup _ chain (source.notes.map createdParsed) source.entries
    (parseBackupNotes_plain_construct source.notes chain source.nonempty source.limit source.grammar source.rendered source.network)
    (by simpa using source.limit) parsed source.commitments
  · intro entry member
    obtain ⟨note, hm, rfl⟩ := List.mem_map.mp member
    exact source.decoded note hm
  · intro entry member
    obtain ⟨note, hm, rfl⟩ := List.mem_map.mp member
    exact source.width note hm

/-- Exact generated seeded-format roundtrip and the same public funding
items. The phrase grammar excludes embedded note tokens; metadata is not an
authenticity claim, and legacy fallback still extracts recoverable raw notes. -/
theorem source_seeded_construct (source : Source chain) (phrase : String)
    (phraseGrammar : seedPhraseGrammar phrase = true)
    (nonces : source.notes.map (·.nonce) = (List.range source.notes.length).map some) :
    ∃ raw, formatDepositBackup source.notes (some phrase) = .ok raw ∧
      parseDepositBackup raw chain = .ok source.entries ∧
      DepositMulti.publicItems raw chain = .ok source.items := by
  have phraseNonempty : phrase.isEmpty = false := by
    cases empty : phrase.isEmpty
    · rfl
    · simp [seedPhraseGrammar, empty] at phraseGrammar
  have parsedNotes := parseBackupNotes_seeded_construct source.notes chain phrase source.limit
    phraseGrammar source.grammar source.rendered source.network nonces
  have parsed : parseDepositBackup (seededBackupText source.notes phrase) chain = .ok source.entries := by
    unfold parseDepositBackup
    rw [parsedNotes]
    exact identifyBackupNotes_construct source.notes source.identities source.nonempty
      source.sameAsset source.distinct source.identity
  refine ⟨seededBackupText source.notes phrase,
    formatDepositBackup_seeded source.notes phrase source.nonempty phraseNonempty, parsed, ?_⟩
  apply publicItems_of_backup _ chain (source.notes.map createdParsed) source.entries parsedNotes
    (by simpa using source.limit) parsed source.commitments
  · intro entry member
    obtain ⟨note, hm, rfl⟩ := List.mem_map.mp member
    exact source.decoded note hm
  · intro entry member
    obtain ⟨note, hm, rfl⟩ := List.mem_map.mp member
    exact source.width note hm

/-- Composition with the actual route planner: the independently decoded
plan is indexed by the public items constructed from the original backup. -/
theorem source_plan_success (source : Source chain) (sender : Nat)
    (readings : DepositMulti.Readings) (forceSequential : Bool) (output : DepositMulti.Plan)
    (built : DepositMulti.plan source.items chain sender readings forceSequential = .ok output) :
    ∃ raw input meaning,
      formatDepositBackup source.notes none = .ok raw ∧
      DepositMulti.publicItems raw chain = .ok source.items ∧
      DepositMulti.planIntent source.items chain sender readings forceSequential = .ok input ∧
      Tornado.Protocol.DepositIntent.expected input = .ok meaning ∧
      Tornado.Protocol.DepositIntent.decodePlan (DepositMulti.planEncoding output) = .ok meaning ∧
      Tornado.Protocol.DepositIntent.PlanPolicy input meaning := by
  obtain ⟨raw, formatted, _, extracted⟩ := source_construct source
  obtain ⟨input, meaning, original, expected, decoded, policy⟩ :=
    DepositMulti.plan_success_decodes source.items chain sender readings forceSequential output built
  exact ⟨raw, input, meaning, formatted, extracted, original, expected, decoded, policy⟩

/-- Every public item starts from a rehashed parsed private note; public
invoice imports have a separate trust boundary and are not covered here. -/
theorem source_identity_provenance (source : Source chain) :
    ∀ entry ∈ source.entries, noteIdentity entry.note = .ok entry.publicIdentity := by
  intro entry member
  obtain ⟨note, hm, rfl⟩ := List.mem_map.mp member
  exact source.identity note hm

def originalIdentity (note : CreatedNote) : NoteIdentity := ⟨note.commitment, note.nullifierHash⟩

def decodedCommitment (entry : BackupIdentity) : ByteArray :=
  (parseHexBytes entry.publicIdentity.commitment).toOption.getD ByteArray.empty

/-- Derive every parser/hex/identity obligation from actual creator provenance.
Only supported catalog, session scope and distinct-source conditions remain. -/
def Source.ofCreated (notes : List CreatedNote) (chain : ChainId)
    (nonempty : notes ≠ []) (limit : notes.length ≤ 100)
    (created : ∀ note ∈ notes, CreatedFromPreimage note)
    (catalog : ∀ note ∈ notes, note.pool ∈ allPools)
    (network : ∀ note ∈ notes, note.pool.chainId = chain)
    (sameAsset : ∀ first ∈ notes, ∀ note ∈ notes,
      note.pool.asset.symbol = first.pool.asset.symbol)
    (distinct : (notes.map (fun note => String.ofList (note.preimage.toList.take 62))).eraseDups.length = notes.length) :
    Source chain := {
  notes, identities := originalIdentity, commitments := decodedCommitment,
  nonempty, limit,
  grammar := fun note member => created_preimage_grammar note (created note member) (catalog note member),
  rendered := fun note member => created_preimage_render note (created note member),
  network, sameAsset, distinct,
  identity := fun note member => created_preimage_identity note (created note member),
  decoded := by
    intro note member
    obtain ⟨bytes, decoded, _⟩ := created_preimage_commitment note (created note member)
    simp only [originalIdentity, decodedCommitment, decoded, Except.toOption, Option.getD_some],
  width := by
    intro note member
    obtain ⟨bytes, decoded, width⟩ := created_preimage_commitment note (created note member)
    simpa only [originalIdentity, decodedCommitment, decoded, Except.toOption, Option.getD_some] using width }

/-- An actual independent-note constructor result supplies all upstream
source evidence for the real backup and funding projection. -/
def Source.ofIndependent (pool : Pool) (nullifierKey secretKey uuid : ByteArray)
    (note : CreatedNote) (built : independentNoteFromEntropy pool nullifierKey secretKey uuid = .ok note)
    (supported : pool ∈ allPools) : Source pool.chainId := by
  have evidence := independentNote_source pool nullifierKey secretKey uuid note built
  have poolEq := createdAtPool_pool pool note evidence
  apply Source.ofCreated [note] pool.chainId (by simp) (by simp)
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact ⟨pool, evidence⟩
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    simpa only [poolEq] using supported
  · intro value member
    simp only [List.mem_singleton] at member
    subst value
    exact congrArg Pool.chainId poolEq
  · intro first member value present
    simp only [List.mem_singleton] at member present
    subst first
    subst value
    rfl
  · rfl

/-- Actual seeded outputs retain their original selected pools, and every
position was produced by the secret-byte constructor through its mnemonic key. -/
def Source.ofSeeded (pools : List Pool) (mnemonic : String) (uuids : List ByteArray)
    (notes : List CreatedNote) (built : seededNotesFromMnemonic pools mnemonic uuids = .ok notes)
    (nonempty : pools ≠ []) (limit : pools.length ≤ 100)
    (catalog : ∀ pool ∈ pools, pool ∈ allPools)
    (network : ∀ pool ∈ pools, pool.chainId = chain)
    (sameAsset : ∀ first ∈ pools, ∀ pool ∈ pools,
      pool.asset.symbol = first.asset.symbol)
    (distinct : (notes.map (fun note => String.ofList (note.preimage.toList.take 62))).eraseDups.length = notes.length) :
    Source chain := by
  have selected := seededNotes_pools pools mnemonic uuids notes built
  have membership : ∀ note ∈ notes, note.pool ∈ pools := by
    intro note member
    have mapped : note.pool ∈ notes.map (·.pool) := List.mem_map_of_mem member
    rwa [selected] at mapped
  have nonemptyNotes : notes ≠ [] := by
    intro empty
    rw [empty] at selected
    simp only [List.map_nil] at selected
    exact nonempty selected.symm
  have count : notes.length = pools.length := by
    simpa only [List.length_map] using congrArg List.length selected
  exact Source.ofCreated notes chain nonemptyNotes (by omega)
    (seededNotes_source pools mnemonic uuids notes built)
    (fun note member => catalog note.pool (membership note member))
    (fun note member => network note.pool (membership note member))
    (fun first member note present => sameAsset first.pool (membership first member) note.pool (membership note present))
    distinct

theorem independent_constructor_backup (pool : Pool) (nullifierKey secretKey uuid : ByteArray)
    (note : CreatedNote) (built : independentNoteFromEntropy pool nullifierKey secretKey uuid = .ok note)
    (supported : pool ∈ allPools) :
    ∃ raw, formatDepositBackup [note] none = .ok raw ∧
      parseDepositBackup raw pool.chainId = .ok (Source.ofIndependent pool nullifierKey secretKey uuid note built supported).entries ∧
      DepositMulti.publicItems raw pool.chainId = .ok (Source.ofIndependent pool nullifierKey secretKey uuid note built supported).items :=
  source_construct (Source.ofIndependent pool nullifierKey secretKey uuid note built supported)

theorem seeded_constructor_backup (pools : List Pool) (mnemonic : String) (uuids : List ByteArray)
    (notes : List CreatedNote) (built : seededNotesFromMnemonic pools mnemonic uuids = .ok notes)
    (nonempty : pools ≠ []) (limit : pools.length ≤ 100)
    (catalog : ∀ pool ∈ pools, pool ∈ allPools)
    (network : ∀ pool ∈ pools, pool.chainId = chain)
    (sameAsset : ∀ first ∈ pools, ∀ pool ∈ pools, pool.asset.symbol = first.asset.symbol)
    (distinct : (notes.map (fun note => String.ofList (note.preimage.toList.take 62))).eraseDups.length = notes.length)
    (phraseGrammar : seedPhraseGrammar mnemonic = true) :
    ∃ raw, formatDepositBackup notes (some mnemonic) = .ok raw ∧
      parseDepositBackup raw chain = .ok (Source.ofSeeded pools mnemonic uuids notes built nonempty limit catalog network sameAsset distinct).entries ∧
      DepositMulti.publicItems raw chain = .ok (Source.ofSeeded pools mnemonic uuids notes built nonempty limit catalog network sameAsset distinct).items :=
  source_seeded_construct
    (Source.ofSeeded pools mnemonic uuids notes built nonempty limit catalog network sameAsset distinct)
    mnemonic phraseGrammar (seededNotes_nonce_range pools mnemonic uuids notes built)

end Tornado.Spec.DepositBackupIntent

#print axioms Tornado.Spec.DepositBackupIntent.publicItemsLoop_construct
#print axioms Tornado.Spec.DepositBackupIntent.publicItems_of_backup
#print axioms Tornado.Spec.DepositBackupIntent.source_construct
#print axioms Tornado.Spec.DepositBackupIntent.source_identity_provenance

#print axioms Tornado.Spec.DepositBackupIntent.source_seeded_construct

#print axioms Tornado.Spec.DepositBackupIntent.source_plan_success

#print axioms Tornado.Spec.DepositBackupIntent.independent_constructor_backup
#print axioms Tornado.Spec.DepositBackupIntent.seeded_constructor_backup
