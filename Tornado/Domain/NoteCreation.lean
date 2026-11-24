import Tornado.Domain.Invoice
import Tornado.Crypto.TornadoSignature

/-!
Pure note creation and backup formatting for the pinned CLI. Randomness and
private file I/O are supplied by the effectful caller.
No function here samples entropy or writes a secret.
-/

namespace Tornado.Domain

open Tornado.Crypto

structure CreatedNote where
  raw : String
  preimage : String
  pool : Pool
  commitment : String
  nullifierHash : String
  id : String
  nonce : Option Nat := none
  call : DepositCall
  -- raw and preimage are spendable secrets, so generic Repr is unsafe.
  deriving BEq, Inhabited

private def bytesLE (value length : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for index in [0:length] do
    result := result.push ((value / 2 ^ (8 * index) % 256).toUInt8)
  return result

private def reversed (bytes : ByteArray) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for index in [0:bytes.size] do
    result := result.push bytes[bytes.size - index - 1]!
  return result

private def byteHex (byte : UInt8) : String :=
  let alphabet := "0123456789abcdef".toList.toArray
  String.ofList [alphabet[byte.toNat / 16]!, alphabet[byte.toNat % 16]!]

/-- Deterministic RFC 4122 version-four UUID from 16 separately supplied
    random bytes. The entropy source is not implemented by this pure module. -/
def uuidV4FromEntropy (entropy : ByteArray) : Except String String := do
  if entropy.size != 16 then throw "UUID entropy must contain exactly 16 bytes."
  let mut bytes := entropy
  bytes := bytes.set! 6 ((bytes[6]!.toNat % 16 + 64).toUInt8)
  bytes := bytes.set! 8 ((bytes[8]!.toNat % 64 + 128).toUInt8)
  let hex := String.join (bytes.data.toList.map byteHex)
  return String.intercalate "-" [
    String.ofList (hex.toList.take 8),
    String.ofList ((hex.toList.drop 8).take 4),
    String.ofList ((hex.toList.drop 12).take 4),
    String.ofList ((hex.toList.drop 16).take 4),
    String.ofList (hex.toList.drop 20)]

private def checkPool (pool : Pool) : Except String Nat := do
  let some known := poolFor pool.chainId pool.denomination pool.asset.symbol
    | throw "This Tornado pool is unavailable."
  if known.address.toLower != pool.address.toLower then
    throw "This Tornado pool is unavailable."
  let address ← parseHexBytes pool.address
  if address.size != 20 then throw "This Tornado pool is unavailable."
  return address.data.foldl (fun value byte => value * 256 + byte.toNat) 0

private def fromPreimage (pool : Pool) (nullifier secret : ByteArray)
    (id : String) (nonce : Option Nat) : Except String CreatedNote := do
  if nullifier.size != 31 || secret.size != 31 then
    throw "Each Classic note secret must contain 31 bytes."
  let preimageBytes := nullifier ++ secret
  let preimage := bytesToHex preimageBytes
  let raw := s!"tornado-{pool.asset.symbol.toLower}-{pool.denomination}-{chainNumber pool.chainId}-0x{preimage}"
  let commitment ← toHex32 (← pedersenX preimageBytes)
  let nullifierHash ← toHex32 (← pedersenX nullifier)
  let deposit ← depositCall pool commitment
  return { raw := raw, preimage := preimage, pool := pool, commitment := commitment,
           nullifierHash := nullifierHash, id := id, nonce := nonce, call := deposit }

/-- Exact SDK `coalesceSecret`: interpret the 32-byte keystore value as a
    big-endian integer, serialize it little-endian, append chain and pool in
    little-endian, Keccak-256, then mask to 248 bits. The mask keeps the first
    31 digest bytes. -/
def legacyCoalescedSecret (key : ByteArray) (chainId poolAddress : Nat) : Except String ByteArray := do
  if key.size != 32 then throw "Legacy keystore key must contain 32 bytes."
  if chainId >= 2 ^ 64 || poolAddress >= 2 ^ 160 then
    throw "Legacy note chain or pool address is out of range."
  return (keccak256 (reversed key ++ bytesLE chainId 8 ++ bytesLE poolAddress 20)).extract 0 31

/-- Pure independent-note derivation from the two *separately sampled* keys
    used by the pinned SDK's keystore paths at deposit index zero. The UUID
    has its own entropy input and does not influence the note secrets. -/
def independentNoteFromEntropy (pool : Pool) (nullifierKey saltKey uuidEntropy : ByteArray) :
    Except String CreatedNote := do
  let address ← checkPool pool
  let nullifier ← legacyCoalescedSecret nullifierKey (chainNumber pool.chainId) address
  let secret ← legacyCoalescedSecret saltKey (chainNumber pool.chainId) address
  let id ← uuidV4FromEntropy uuidEntropy
  fromPreimage pool nullifier secret id none

/-- One seeded position. UUID entropy supplies only the presentation ID. -/
def seededNoteAt (privateKey : ByteArray) (pool : Pool) (nonce : Nat) (uuid : ByteArray) :
    Except String CreatedNote := do
  let address ← checkPool pool
  let derived ← tornadoSignatureNote privateKey (chainNumber pool.chainId) nonce address
  let id ← uuidV4FromEntropy uuid
  fromPreimage pool derived.nullifierBytes derived.secretBytes id (some nonce)

def seededWithKey (privateKey : ByteArray) (pools : List Pool) (uuidEntropy : List ByteArray) :
    Except String (List CreatedNote) := do
  let mut result := []
  for (pool, nonce) in pools.zipIdx do
    result := result ++ [← seededNoteAt privateKey pool nonce uuidEntropy[nonce]!]
  return result

/-- Seeded session recovery derives one note per selected pool with a
    contiguous nonce sequence, sharing the native BIP32 signing key. The
    supplied UUID inputs are independent of the mnemonic and note secrets. -/
def validateSeededInputs (pools : List Pool) (uuidEntropy : List ByteArray) : Except String Unit := do
  let some first := pools.head? | throw "Choose at least one note."
  if pools.length != uuidEntropy.length then
    throw "Each note needs its own UUID entropy."
  if uuidEntropy.eraseDups.length != uuidEntropy.length then
    throw "Each note needs distinct UUID entropy."
  let _ ← checkPool first
  for pool in pools do
    let _ ← checkPool pool
    if pool.chainId != first.chainId || pool.asset.symbol != first.asset.symbol then
      throw "Use supported pools of one asset on one network per deposit session."
  return ()

def seededNotesFromMnemonic (pools : List Pool) (mnemonic : String)
    (uuidEntropy : List ByteArray) : Except String (List CreatedNote) := do
  validateSeededInputs pools uuidEntropy
  let signingKey ← tornadoNoteSigningKeyFromMnemonic mnemonic
  seededWithKey signingKey.privateKey pools uuidEntropy

def rawBackup (notes : List CreatedNote) : String :=
  String.intercalate "\n" (notes.map (·.raw)) ++ "\n"

def derivationReference : String :=
  "https://github.com/ethereum/kohaku/blob/886f72ddd6e36d43e53675fc359fd4a315590ee8/packages/tornado-cash/src/account/signature-keys.ts"

def seedKeyReference : String :=
  "https://github.com/ethereum/kohaku/blob/886f72ddd6e36d43e53675fc359fd4a315590ee8/packages/plugins/src/host/mnemonic-keystore.ts"

/-- Exact user-facing backup text produced by the pinned CLI. The caller
    must durably create a protected file before using it for real deposits. -/
def legacyFormatDepositBackup (notes : List CreatedNote) (seedPhrase : Option String := none) :
    Except String String := do
  let raw := rawBackup notes
  match seedPhrase with
  | none => return raw
  | some phrase =>
    if phrase.isEmpty then return raw
    if notes.isEmpty then throw "There are no notes to back up."
    let nonceList := String.intercalate ", " (notes.map fun note =>
      match note.nonce with | none => "" | some nonce => toString nonce)
    return "------- SEED PHRASE (SECRET) --------\n" ++ phrase ++
      "\n-------------------------------------\n\n" ++
      "-------- NOTES (SECRET) --------\n" ++ raw ++
      "--------------------------------\n\n" ++
      "-------- METADATA --------\n" ++
      "Anyone with the seed phrase above can find and control ALL of these Tornado notes.\n" ++
      "Each individual note string is also secret material: anyone with access to it can spend that note.\n\n" ++
      s!"Note nonces: {nonceList} (in the same order as the notes above).\n\n" ++
      "Exact note derivation reference (Kohaku SDK, fixed commit):\n" ++
      derivationReference ++ "\n\n" ++
      "Seed-to-key implementation (same commit):\n" ++ seedKeyReference ++ "\n" ++
      "--------------------------\n"

def seedNonceText (nonces : List (Option Nat)) : String :=
  String.intercalate ", " (nonces.map fun nonce =>
    match nonce with | none => "" | some nonce => toString nonce)

def seedHeaderLines (phrase : String) : List String :=
  ["------- SEED PHRASE (SECRET) --------", phrase,
    "-------------------------------------", "", "-------- NOTES (SECRET) --------"]

def seedNoteFooter : String := "--------------------------------"

def seedTailText (nonceText : String) : String :=
  "\n-------- METADATA --------\n" ++
  "Anyone with the seed phrase above can find and control ALL of these Tornado notes.\n" ++
  "Each individual note string is also secret material: anyone with access to it can spend that note.\n\n" ++
  s!"Note nonces: {nonceText} (in the same order as the notes above).\n\n" ++
  "Exact note derivation reference (Kohaku SDK, fixed commit):\n" ++
  derivationReference ++ "\n\n" ++
  "Seed-to-key implementation (same commit):\n" ++ seedKeyReference ++ "\n" ++
  "--------------------------\n"

def seededBackupText (notes : List CreatedNote) (phrase : String) : String :=
  CanonicalText.joinString '\n' (seedHeaderLines phrase ++ notes.map (·.raw) ++
    [seedNoteFooter, seedTailText (seedNonceText (notes.map (·.nonce)))])

def formatDepositBackup (notes : List CreatedNote) (seedPhrase : Option String := none) :
    Except String String := do
  match seedPhrase with
  | none => return rawBackup notes
  | some phrase =>
    if phrase.isEmpty then return rawBackup notes
    if notes.isEmpty then throw "There are no notes to back up."
    return seededBackupText notes phrase

theorem formatDepositBackup_seeded (notes : List CreatedNote) (phrase : String)
    (nonempty : notes ≠ []) (phraseNonempty : phrase.isEmpty = false) :
    formatDepositBackup notes (some phrase) = .ok (seededBackupText notes phrase) := by
  simp [formatDepositBackup, nonempty, phraseNonempty, pure, Except.pure,
    bind, Except.bind, List.isEmpty_iff]


def recoverableFields (note : CreatedNote) :
    String × String × Pool × String × String × Option Nat :=
  (note.raw, note.preimage, note.pool, note.commitment, note.nullifierHash, note.nonce)

/-- The only UUID-dependent field is the presentation ID, not a spendable
secret, public identifier, selected pool or recovery nonce. -/
theorem fromPreimage_uuid_independent (pool : Pool) (nullifier secret : ByteArray)
    (idLeft idRight : String) (nonce : Option Nat) (left right : CreatedNote)
    (hl : fromPreimage pool nullifier secret idLeft nonce = .ok left)
    (hr : fromPreimage pool nullifier secret idRight nonce = .ok right) :
    recoverableFields left = recoverableFields right := by
  unfold fromPreimage at hl hr
  simp only [bind, Except.bind] at hl hr
  split at hl
  · contradiction
  · rename_i bounds
    simp only [bounds] at hr
    cases hc : pedersenX (nullifier ++ secret) with
    | error message => simp only [hc] at hl; contradiction
    | ok commitment =>
      cases hh : toHex32 commitment with
      | error message => simp only [hc, hh] at hl; contradiction
      | ok commitmentText =>
        cases hn : pedersenX nullifier with
        | error message => simp only [hc, hh, hn] at hl; contradiction
        | ok nullifierHash =>
          cases hx : toHex32 nullifierHash with
          | error message => simp only [hc, hh, hn, hx] at hl; contradiction
          | ok nullifierText =>
            cases hd : depositCall pool commitmentText with
            | error message => simp only [hc, hh, hn, hx, hd] at hl; contradiction
            | ok call =>
              simp only [hc, hh, hn, hx, hd, pure, Except.pure, Except.ok.injEq] at hl hr
              cases hl
              cases hr
              rfl

/-- A formatter law for arbitrary note lists, independent of parsing. -/
theorem rawBackup_canonical (notes : List CreatedNote) (nonempty : notes ≠ []) :
    rawBackup notes = CanonicalText.joinString '\n' (notes.map (·.raw) ++ [""]) := by
  rw [CanonicalText.joinString_append '\n' _ [""] (by simpa using nonempty) (by simp)]
  rw [CanonicalText.joinString_eq_intercalate]
  have newline : String.ofList ['\n'] = "\n" := by decide
  rw [newline]
  simp [rawBackup, CanonicalText.joinString, CanonicalText.join]

theorem formatDepositBackup_plain (notes : List CreatedNote) (nonempty : notes ≠ []) :
    formatDepositBackup notes none =
      .ok (CanonicalText.joinString '\n' (notes.map (·.raw) ++ [""])) := by
  simp only [formatDepositBackup, rawBackup_canonical notes nonempty]
  rfl

/-- The creator's raw note renderer is exactly the canonical grammar renderer. -/
theorem fromPreimage_render (pool : Pool) (nullifier secret : ByteArray)
    (id : String) (nonce : Option Nat) (note : CreatedNote)
    (created : fromPreimage pool nullifier secret id nonce = .ok note) :
    note.raw = renderNoteText note.pool note.preimage ∧ note.pool = pool ∧
      note.preimage = bytesToHex (nullifier ++ secret) ∧ note.nonce = nonce := by
  unfold fromPreimage at created
  simp only [bind, Except.bind] at created
  split at created
  · contradiction
  · cases hc : pedersenX (nullifier ++ secret) with
    | error message => simp only [hc] at created; contradiction
    | ok commitment =>
      cases hh : toHex32 commitment with
      | error message => simp only [hc, hh] at created; contradiction
      | ok commitmentText =>
        cases hn : pedersenX nullifier with
        | error message => simp only [hc, hh, hn] at created; contradiction
        | ok nullifierHash =>
          cases hx : toHex32 nullifierHash with
          | error message => simp only [hc, hh, hn, hx] at created; contradiction
          | ok nullifierText =>
            cases hd : depositCall pool commitmentText with
            | error message => simp only [hc, hh, hn, hx, hd] at created; contradiction
            | ok call =>
              simp only [hc, hh, hn, hx, hd, pure, Except.pure, Except.ok.injEq] at created
              cases created
              exact ⟨(renderNoteText_legacy _ _).symm, rfl, rfl, rfl⟩

theorem seededNoteAt_nonce (privateKey : ByteArray) (pool : Pool) (nonce : Nat)
    (uuid : ByteArray) (note : CreatedNote)
    (created : seededNoteAt privateKey pool nonce uuid = .ok note) : note.nonce = some nonce := by
  unfold seededNoteAt at created
  simp only [bind, Except.bind] at created
  cases address : checkPool pool with
  | error message => simp only [address] at created; contradiction
  | ok target =>
    cases derived : tornadoSignatureNote privateKey (chainNumber pool.chainId) nonce target with
    | error message => simp only [address, derived] at created; contradiction
    | ok material =>
      cases id : uuidV4FromEntropy uuid with
      | error message => simp only [address, derived, id] at created; contradiction
      | ok text =>
        have result : fromPreimage pool material.nullifierBytes material.secretBytes text (some nonce) = .ok note := by
          simpa only [address, derived, id] using created
        exact (fromPreimage_render _ _ _ _ _ _ result).2.2.2

theorem seededNoteAt_uuid_independent (privateKey : ByteArray) (pool : Pool) (nonce : Nat)
    (uuidLeft uuidRight : ByteArray) (left right : CreatedNote)
    (hl : seededNoteAt privateKey pool nonce uuidLeft = .ok left)
    (hr : seededNoteAt privateKey pool nonce uuidRight = .ok right) :
    recoverableFields left = recoverableFields right := by
  unfold seededNoteAt at hl hr
  simp only [bind, Except.bind] at hl hr
  cases address : checkPool pool with
  | error message => simp only [address] at hl; contradiction
  | ok target =>
    cases derived : tornadoSignatureNote privateKey (chainNumber pool.chainId) nonce target with
    | error message => simp only [address, derived] at hl; contradiction
    | ok material =>
      cases il : uuidV4FromEntropy uuidLeft with
      | error message => simp only [address, derived, il] at hl; contradiction
      | ok idLeft =>
        cases ir : uuidV4FromEntropy uuidRight with
        | error message => simp only [address, derived, ir] at hr; contradiction
        | ok idRight =>
          exact fromPreimage_uuid_independent pool material.nullifierBytes material.secretBytes
            idLeft idRight (some nonce) left right
            (by simpa only [address, derived, il] using hl)
            (by simpa only [address, derived, ir] using hr)

def collectCreated (source : List α) (run : α → Except String CreatedNote)
    (initial : List CreatedNote) : Except String (List CreatedNote) := do
  let mut output := initial
  for input in source do output := output ++ [← run input]
  return output

theorem collectCreated_eq_mapM (source : List α) (run : α → Except String CreatedNote)
    (initial : List CreatedNote) :
    collectCreated source run initial = do
      let values ← source.mapM run
      return initial ++ values := by
  induction source generalizing initial with
  | nil => simp [collectCreated, bind, Except.bind, pure, Except.pure]
  | cons first rest ih =>
    cases head : run first with
    | error message =>
      simp [collectCreated, List.forIn_cons, head, List.mapM_cons, bind, Except.bind]
    | ok note =>
      simp only [collectCreated, List.forIn_cons, head, bind, Except.bind, pure, Except.pure]
      change collectCreated rest run (initial ++ [note]) = _
      rw [ih]
      cases tail : rest.mapM run <;>
        simp [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure, List.append_assoc]

theorem seededWithKey_eq_mapM (privateKey : ByteArray) (pools : List Pool)
    (uuids : List ByteArray) :
    seededWithKey privateKey pools uuids = pools.zipIdx.mapM (fun entry =>
      seededNoteAt privateKey entry.1 entry.2 uuids[entry.2]!) := by
  change collectCreated pools.zipIdx (fun entry =>
    seededNoteAt privateKey entry.1 entry.2 uuids[entry.2]!) [] = _
  rw [collectCreated_eq_mapM]
  cases result : pools.zipIdx.mapM (fun entry =>
    seededNoteAt privateKey entry.1 entry.2 uuids[entry.2]!) <;> rfl

/-- Ordered projection of an actual successful Except-map traversal. -/
theorem mapM_output_projection (source : List α) (run : α → Except String CreatedNote)
    (output : List CreatedNote) (project : CreatedNote → β) (expected : α → β)
    (built : source.mapM run = .ok output)
    (pointwise : ∀ input ∈ source, ∀ note, run input = .ok note → project note = expected input) :
    output.map project = source.map expected := by
  induction source generalizing output with
  | nil =>
    simp [pure, Except.pure] at built
    subst output
    rfl
  | cons first rest ih =>
    simp only [List.mapM_cons] at built
    cases head : run first with
    | error message => simp [head, bind, Except.bind] at built
    | ok note =>
      cases tail : rest.mapM run with
      | error message => simp [head, tail, bind, Except.bind] at built
      | ok notes =>
        simp [head, tail, bind, Except.bind, pure, Except.pure] at built
        subst output
        simp only [List.map_cons, pointwise first (by simp) note head]
        congr 1
        exact ih notes tail (fun input member result h => pointwise input (by simp [member]) result h)

theorem seededWithKey_nonces (privateKey : ByteArray) (pools : List Pool)
    (uuids : List ByteArray) (notes : List CreatedNote)
    (built : seededWithKey privateKey pools uuids = .ok notes) :
    notes.map (·.nonce) = pools.zipIdx.map (fun entry => some entry.2) := by
  rw [seededWithKey_eq_mapM] at built
  exact mapM_output_projection pools.zipIdx _ notes (·.nonce) (fun entry => some entry.2) built
    (by intro entry _ note result; exact seededNoteAt_nonce privateKey entry.1 entry.2 _ note result)

/-- Success of the actual mnemonic creator is tied to its actual mnemonic
key derivation and to the indexed per-pool loop. -/
theorem seededNotes_success (pools : List Pool) (mnemonic : String) (uuids : List ByteArray)
    (notes : List CreatedNote) (built : seededNotesFromMnemonic pools mnemonic uuids = .ok notes) :
    ∃ signingKey, tornadoNoteSigningKeyFromMnemonic mnemonic = .ok signingKey ∧
      seededWithKey signingKey.privateKey pools uuids = .ok notes := by
  unfold seededNotesFromMnemonic at built
  cases validated : validateSeededInputs pools uuids with
  | error message => simp [validated, bind, Except.bind] at built
  | ok valid =>
    cases key : tornadoNoteSigningKeyFromMnemonic mnemonic with
    | error message => simp [validated, key, bind, Except.bind] at built
    | ok signingKey =>
      exact ⟨signingKey, rfl, by simpa [validated, key, bind, Except.bind] using built⟩

theorem seededNotes_contiguous_nonces (pools : List Pool) (mnemonic : String)
    (uuids : List ByteArray) (notes : List CreatedNote)
    (built : seededNotesFromMnemonic pools mnemonic uuids = .ok notes) :
    notes.map (·.nonce) = pools.zipIdx.map (fun entry => some entry.2) := by
  obtain ⟨signingKey, _, derived⟩ := seededNotes_success pools mnemonic uuids notes built
  exact seededWithKey_nonces signingKey.privateKey pools uuids notes derived

theorem seededNotes_nonce_range (pools : List Pool) (mnemonic : String)
    (uuids : List ByteArray) (notes : List CreatedNote)
    (built : seededNotesFromMnemonic pools mnemonic uuids = .ok notes) :
    notes.map (·.nonce) = (List.range notes.length).map some := by
  have ordered := seededNotes_contiguous_nonces pools mnemonic uuids notes built
  have count : notes.length = pools.length := by
    simpa only [List.length_map, List.length_zipIdx] using congrArg List.length ordered
  have ranges := congrArg (List.map some) (List.zipIdx_map_snd 0 pools)
  simp only [List.map_map] at ranges
  rw [ordered, count]
  simpa only [List.range_eq_range', Function.comp_apply] using ranges

theorem fromPreimage_widths (pool : Pool) (nullifier secret : ByteArray)
    (id : String) (nonce : Option Nat) (note : CreatedNote)
    (created : fromPreimage pool nullifier secret id nonce = .ok note) :
    nullifier.size = 31 ∧ secret.size = 31 := by
  by_cases nullWidth : nullifier.size = 31
  · by_cases secretWidth : secret.size = 31
    · exact ⟨nullWidth, secretWidth⟩
    · simp [fromPreimage, nullWidth, secretWidth, bind, Except.bind] at created
  · simp [fromPreimage, nullWidth, bind, Except.bind] at created

theorem fromPreimage_encodings (pool : Pool) (nullifier secret : ByteArray)
    (id : String) (nonce : Option Nat) (note : CreatedNote)
    (created : fromPreimage pool nullifier secret id nonce = .ok note) :
    ∃ commitment nullifierHash,
      pedersenX (nullifier ++ secret) = .ok commitment ∧ pedersenX nullifier = .ok nullifierHash ∧
      toHex32 commitment = .ok note.commitment ∧ toHex32 nullifierHash = .ok note.nullifierHash := by
  obtain ⟨nullWidth, secretWidth⟩ := fromPreimage_widths pool nullifier secret id nonce note created
  unfold fromPreimage at created
  simp only [nullWidth, secretWidth, bne_self_eq_false, Bool.false_or, Bool.false_eq_true,
    ↓reduceIte, bind, Except.bind] at created
  cases hc : pedersenX (nullifier ++ secret) with
  | error message => simp only [hc] at created; contradiction
  | ok commitment =>
    cases hh : toHex32 commitment with
    | error message => simp only [hc, hh] at created; contradiction
    | ok commitmentText =>
      cases hn : pedersenX nullifier with
      | error message => simp only [hc, hh, hn] at created; contradiction
      | ok nullifierHash =>
        cases hx : toHex32 nullifierHash with
        | error message => simp only [hc, hh, hn, hx] at created; contradiction
        | ok nullifierText =>
          cases hd : depositCall pool commitmentText with
          | error message => simp only [hc, hh, hn, hx, hd] at created; contradiction
          | ok call =>
            simp only [hc, hh, hn, hx, hd, pure, Except.pure, Except.ok.injEq] at created
            cases created
            exact ⟨commitment, nullifierHash, rfl, rfl, hh, hx⟩

/-- Re-parsing the actual creator's hex reproduces its exact native Pedersen
inputs, so the parser recomputes exactly the public identifiers stored by
creation. This is functional correspondence, not Pedersen security. -/
theorem fromPreimage_noteIdentity (pool : Pool) (nullifier secret : ByteArray)
    (id : String) (nonce : Option Nat) (note : CreatedNote)
    (created : fromPreimage pool nullifier secret id nonce = .ok note) :
    noteIdentity ⟨note.raw, note.preimage, note.pool⟩ =
      .ok ⟨note.commitment, note.nullifierHash⟩ := by
  obtain ⟨nullWidth, secretWidth⟩ := fromPreimage_widths pool nullifier secret id nonce note created
  have preimage := (fromPreimage_render pool nullifier secret id nonce note created).2.2.1
  obtain ⟨commitment, nullifierHash, fullHash, nullHash, commitmentHex, nullHex⟩ :=
    fromPreimage_encodings pool nullifier secret id nonce note created
  have totalWidth : (nullifier ++ secret).size = 62 := by
    simp [ByteArray.size_append, nullWidth, secretWidth]
  have first : (nullifier ++ secret).extract 0 31 = nullifier :=
    ByteArray.extract_append_eq_left nullWidth.symm
  unfold noteIdentity
  simp only [preimage, bytesToHex_length, totalWidth,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind,
    pure, Except.pure, parseHexBytes_bytesToHex, fullHash, first, nullHash, commitmentHex, nullHex]


/-- Concrete provenance in the actual secret-byte constructor. This is a
source-construction fact, not successful parsing or successful validation. -/
def CreatedAtPool (pool : Pool) (note : CreatedNote) : Prop :=
  ∃ nullifier secret id nonce, fromPreimage pool nullifier secret id nonce = .ok note

def CreatedFromPreimage (note : CreatedNote) : Prop := ∃ pool, CreatedAtPool pool note

theorem createdAtPool_pool (pool : Pool) (note : CreatedNote) (source : CreatedAtPool pool note) :
    note.pool = pool := by
  obtain ⟨nullifier, secret, id, nonce, built⟩ := source
  exact (fromPreimage_render pool nullifier secret id nonce note built).2.1

theorem independentNote_source (pool : Pool) (nullifierKey secretKey uuid : ByteArray)
    (note : CreatedNote) (built : independentNoteFromEntropy pool nullifierKey secretKey uuid = .ok note) :
    CreatedAtPool pool note := by
  unfold independentNoteFromEntropy at built
  simp only [bind, Except.bind] at built
  cases hp : checkPool pool with
  | error message => simp only [hp] at built; contradiction
  | ok address =>
    cases hn : legacyCoalescedSecret nullifierKey (chainNumber pool.chainId) address with
    | error message => simp only [hp, hn] at built; contradiction
    | ok nullifier =>
      cases hs : legacyCoalescedSecret secretKey (chainNumber pool.chainId) address with
      | error message => simp only [hp, hn, hs] at built; contradiction
      | ok secret =>
        cases hi : uuidV4FromEntropy uuid with
        | error message => simp only [hp, hn, hs, hi] at built; contradiction
        | ok id =>
          exact ⟨nullifier, secret, id, none, by simpa only [hp, hn, hs, hi] using built⟩

theorem seededNoteAt_source (privateKey : ByteArray) (pool : Pool) (nonce : Nat) (uuid : ByteArray)
    (note : CreatedNote) (built : seededNoteAt privateKey pool nonce uuid = .ok note) :
    CreatedAtPool pool note := by
  unfold seededNoteAt at built
  simp only [bind, Except.bind] at built
  cases hp : checkPool pool with
  | error message => simp only [hp] at built; contradiction
  | ok address =>
    cases hd : tornadoSignatureNote privateKey (chainNumber pool.chainId) nonce address with
    | error message => simp only [hp, hd] at built; contradiction
    | ok derived =>
      cases hi : uuidV4FromEntropy uuid with
      | error message => simp only [hp, hd, hi] at built; contradiction
      | ok id =>
        exact ⟨derived.nullifierBytes, derived.secretBytes, id, some nonce,
          by simpa only [hp, hd, hi] using built⟩

theorem created_preimage_grammar (note : CreatedNote) (source : CreatedFromPreimage note)
    (supported : note.pool ∈ allPools) : CanonicalNoteGrammar note.pool note.preimage := by
  obtain ⟨pool, nullifier, secret, id, nonce, built⟩ := source
  obtain ⟨hn, hs⟩ := fromPreimage_widths pool nullifier secret id nonce note built
  have encoded := (fromPreimage_render pool nullifier secret id nonce note built).2.2.1
  have total : (nullifier ++ secret).size = 62 := by simp [ByteArray.size_append, hn, hs]
  apply canonicalNoteGrammar_hex note.pool note.preimage supported
  · rw [encoded, bytesToHex_length, total]
  · rw [encoded]
    exact bytesToHex_lexical _
  · rw [encoded]
    exact bytesToHex_lower _

theorem created_preimage_identity (note : CreatedNote) (source : CreatedFromPreimage note) :
    noteIdentity ⟨note.raw, note.preimage, note.pool⟩ = .ok ⟨note.commitment, note.nullifierHash⟩ := by
  obtain ⟨pool, nullifier, secret, id, nonce, built⟩ := source
  exact fromPreimage_noteIdentity pool nullifier secret id nonce note built

theorem created_preimage_commitment (note : CreatedNote) (source : CreatedFromPreimage note) :
    ∃ bytes, parseHexBytes note.commitment = .ok bytes ∧ bytes.size = 32 := by
  obtain ⟨pool, nullifier, secret, id, nonce, built⟩ := source
  obtain ⟨commitment, _, _, _, encoded, _⟩ := fromPreimage_encodings pool nullifier secret id nonce note built
  obtain ⟨bytes, decoded, width, _, _⟩ := toHex32_success_bytes commitment note.commitment encoded
  exact ⟨bytes, decoded, width⟩

theorem created_preimage_render (note : CreatedNote) (source : CreatedFromPreimage note) :
    note.raw = renderNoteText note.pool note.preimage := by
  obtain ⟨pool, nullifier, secret, id, nonce, built⟩ := source
  exact (fromPreimage_render pool nullifier secret id nonce note built).1

theorem seededWithKey_pools (privateKey : ByteArray) (pools : List Pool) (uuids : List ByteArray)
    (notes : List CreatedNote) (built : seededWithKey privateKey pools uuids = .ok notes) :
    notes.map (·.pool) = pools := by
  rw [seededWithKey_eq_mapM] at built
  have projection := mapM_output_projection pools.zipIdx _ notes (·.pool) (fun entry => entry.1) built
    (by
      intro entry _ note result
      exact createdAtPool_pool entry.1 note (seededNoteAt_source privateKey entry.1 entry.2 _ note result))
  exact projection.trans (List.zipIdx_map_fst 0 pools)

theorem seededNotes_pools (pools : List Pool) (mnemonic : String) (uuids : List ByteArray)
    (notes : List CreatedNote) (built : seededNotesFromMnemonic pools mnemonic uuids = .ok notes) :
    notes.map (·.pool) = pools := by
  obtain ⟨key, _, derived⟩ := seededNotes_success pools mnemonic uuids notes built
  exact seededWithKey_pools key.privateKey pools uuids notes derived

theorem seededNotes_source (pools : List Pool) (mnemonic : String) (uuids : List ByteArray)
    (notes : List CreatedNote) (built : seededNotesFromMnemonic pools mnemonic uuids = .ok notes) :
    ∀ note ∈ notes, CreatedFromPreimage note := by
  obtain ⟨key, _, derived⟩ := seededNotes_success pools mnemonic uuids notes built
  rw [seededWithKey_eq_mapM] at derived
  have all := mapM_output_projection pools.zipIdx _ notes CreatedFromPreimage (fun _ => True) derived
    (by
      intro entry _ note result
      apply propext
      exact iff_true_intro ⟨entry.1, seededNoteAt_source key.privateKey entry.1 entry.2 _ note result⟩)
  intro note member
  have propertyMember : CreatedFromPreimage note ∈ notes.map CreatedFromPreimage := List.mem_map_of_mem member
  rw [all] at propertyMember
  obtain ⟨_, _, exactProperty⟩ := List.mem_map.mp propertyMember
  exact exactProperty ▸ True.intro

end Tornado.Domain

#print axioms Tornado.Domain.rawBackup_canonical
#print axioms Tornado.Domain.formatDepositBackup_plain
#print axioms Tornado.Domain.fromPreimage_render

#print axioms Tornado.Domain.fromPreimage_uuid_independent

#print axioms Tornado.Domain.seededNoteAt_nonce
#print axioms Tornado.Domain.seededNoteAt_uuid_independent
#print axioms Tornado.Domain.collectCreated_eq_mapM
#print axioms Tornado.Domain.seededWithKey_eq_mapM

#print axioms Tornado.Domain.mapM_output_projection
#print axioms Tornado.Domain.seededWithKey_nonces
#print axioms Tornado.Domain.seededNotes_success
#print axioms Tornado.Domain.seededNotes_contiguous_nonces

#print axioms Tornado.Domain.formatDepositBackup_seeded

#print axioms Tornado.Domain.seededNotes_nonce_range

#print axioms Tornado.Domain.fromPreimage_widths
#print axioms Tornado.Domain.fromPreimage_encodings
#print axioms Tornado.Domain.fromPreimage_noteIdentity

#print axioms Tornado.Domain.createdAtPool_pool
#print axioms Tornado.Domain.independentNote_source
#print axioms Tornado.Domain.seededNoteAt_source
#print axioms Tornado.Domain.created_preimage_grammar
#print axioms Tornado.Domain.created_preimage_identity
#print axioms Tornado.Domain.created_preimage_commitment
#print axioms Tornado.Domain.created_preimage_render
#print axioms Tornado.Domain.seededWithKey_pools
#print axioms Tornado.Domain.seededNotes_pools
#print axioms Tornado.Domain.seededNotes_source
