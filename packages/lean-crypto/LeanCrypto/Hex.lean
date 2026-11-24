import Std
import Init.Data.String.Lemmas.Pattern.String.ForwardPattern
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace LeanCrypto.Hex

def digits : Array Char := "0123456789abcdef".toList.toArray

def byteChars (byte : UInt8) : List Char :=
  [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!]

def encodeList (bytes : List UInt8) : List Char := bytes.flatMap byteChars

def encode (bytes : ByteArray) : String := String.ofList (encodeList bytes.data.toList)

def nibble (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

def decodePair (high low : Char) : Option UInt8 := do
  let hi ← nibble high
  let lo ← nibble low
  return UInt8.ofNat (hi * 16 + lo)

def decodeList : List Char → Except String (List UInt8)
  | [] => .ok []
  | high :: low :: rest =>
      match decodePair high low with
      | none => .error "Hex input contains a non-hex digit."
      | some byte => do return byte :: (← decodeList rest)
  | [_] => .error "Hex input has an odd number of digits."

/-- Tail-recursive executable decoder; the recursive decoder is a proof
reference only and is not used on untrusted runtime text. -/
def decodeLoop : List Char → List UInt8 → Except String (List UInt8)
  | [], collected => .ok collected.reverse
  | high :: low :: rest, collected =>
      match decodePair high low with
      | none => .error "Hex input contains a non-hex digit."
      | some byte => decodeLoop rest (byte :: collected)
  | [_], _ => .error "Hex input has an odd number of digits."

theorem byte_pair_inverse (byte : UInt8) :
    decodePair (digits[byte.toNat / 16]!) (digits[byte.toNat % 16]!) = some byte := by
  have finite : ∀ value : Fin 256,
      decodePair (digits[value.val / 16]!) (digits[value.val % 16]!) = some (UInt8.ofNat value.val) := by
    decide
  simpa only [UInt8.ofNat_toNat] using finite ⟨byte.toNat, byte.toNat_lt_size⟩

theorem encodeList_fold (bytes : List UInt8) (initial : String) :
    bytes.foldl (fun acc byte =>
      (acc.push (digits[byte.toNat / 16]!)).push (digits[byte.toNat % 16]!)) initial =
      initial ++ String.ofList (encodeList bytes) := by
  induction bytes generalizing initial with
  | nil => simp [encodeList]
  | cons byte rest ih =>
    simp only [List.foldl_cons, ih, encodeList, List.flatMap_cons]
    apply String.toList_inj.mp
    simp [String.toList_append, String.toList_push, byteChars, List.append_assoc]

def lowerHex (char : Char) : Bool :=
  ('0' ≤ char && char ≤ '9') || ('a' ≤ char && char ≤ 'f')

theorem byte_chars_lexical (byte : UInt8) :
    (byteChars byte).all lowerHex = true ∧
      (byteChars byte).map Char.toLower = byteChars byte := by
  have finite : ∀ value : Fin 256,
      (byteChars (UInt8.ofNat value.val)).all lowerHex = true ∧
        (byteChars (UInt8.ofNat value.val)).map Char.toLower = byteChars (UInt8.ofNat value.val) := by
    decide
  simpa only [UInt8.ofNat_toNat] using finite ⟨byte.toNat, byte.toNat_lt_size⟩

theorem encodeList_length (bytes : List UInt8) : (encodeList bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    change (byteChars byte ++ encodeList rest).length = _
    rw [List.length_append, ih]
    simp [byteChars]
    omega

theorem encodeList_lexical (bytes : List UInt8) : (encodeList bytes).all lowerHex = true := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [encodeList, List.flatMap_cons, List.all_append]
    rw [(byte_chars_lexical byte).1]
    exact ih

theorem encodeList_lower (bytes : List UInt8) :
    (encodeList bytes).map Char.toLower = encodeList bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    simp only [encodeList, List.flatMap_cons, List.map_append]
    rw [(byte_chars_lexical byte).2]
    exact congrArg (byteChars byte ++ ·) ih

theorem encode_length (bytes : ByteArray) : (encode bytes).length = 2 * bytes.size := by
  simp only [encode, String.length_ofList, encodeList_length, Array.length_toList, ByteArray.size]

theorem encode_lexical (bytes : ByteArray) : (encode bytes).toList.all lowerHex = true := by
  simpa only [encode, String.toList_ofList] using encodeList_lexical bytes.data.toList

theorem encode_lower (bytes : ByteArray) : (encode bytes).toLower = encode bytes := by
  apply String.toList_inj.mp
  simp only [String.toLower, String.toList_map, encode, String.toList_ofList]
  exact encodeList_lower bytes.data.toList

theorem decodeList_encodeList (bytes : List UInt8) :
    decodeList (encodeList bytes) = .ok bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    change (match decodePair (digits[byte.toNat / 16]!) (digits[byte.toNat % 16]!) with
      | none => Except.error "Hex input contains a non-hex digit."
      | some value => do return value :: (← decodeList (encodeList rest))) = .ok (byte :: rest)
    rw [byte_pair_inverse byte, ih]
    rfl

theorem decodeLoop_reference (chars : List Char) (collected : List UInt8) :
    decodeLoop chars collected = (decodeList chars).map (fun rest => collected.reverse ++ rest) := by
  cases chars with
  | nil => simp [decodeLoop, decodeList, Except.map]
  | cons high tail =>
    cases tail with
    | nil => rfl
    | cons low rest =>
      cases pair : decodePair high low with
      | none => simp [decodeLoop, decodeList, pair, Except.map]
      | some byte =>
        simp only [decodeLoop, decodeList, pair]
        rw [decodeLoop_reference rest (byte :: collected)]
        cases decoded : decodeList rest <;>
          simp [bind, Except.bind, pure, Except.pure, Except.map,
            List.reverse_cons, List.append_assoc]
termination_by chars.length

def decodeChars (chars : List Char) : Except String ByteArray :=
  if chars.length % 2 != 0 then .error "Hex input has an odd number of digits."
  else (decodeLoop chars []).map (fun bytes => ⟨bytes.toArray⟩)

def decode (raw : String) : Except String ByteArray :=
  decodeChars (if raw.startsWith "0x" then raw.toList.drop 2 else raw.toList)

theorem decodeChars_encodeList (bytes : List UInt8) :
    decodeChars (encodeList bytes) = .ok ⟨bytes.toArray⟩ := by
  unfold decodeChars
  rw [encodeList_length]
  simp only [Nat.mul_mod_right, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [decodeLoop_reference, decodeList_encodeList]
  rfl

theorem startsWith_iff_append (text prefixText : String) (nonempty : prefixText.isEmpty = false) :
    text.startsWith prefixText = true ↔ ∃ tail, text = prefixText ++ tail := by
  have hn : prefixText.toSlice.isEmpty = false := by simpa using nonempty
  letI := String.Slice.Pattern.Model.ForwardSliceSearcher.lawfulForwardPatternModel hn
  change String.Slice.Pattern.ForwardPattern.startsWith prefixText.toSlice text.toSlice = true ↔ _
  rw [String.Slice.Pattern.LawfulForwardPattern.startsWith_eq]
  have noPrefix := String.Slice.Pattern.Model.LawfulForwardPatternModel.dropPrefix?_eq_none_iff
    (pat := prefixText.toSlice) (p₀ := text.toSlice.startPos)
  rw [String.Slice.Pattern.Model.ForwardSliceSearcher.matchesAt_iff_splits hn] at noPrefix
  simp at noPrefix
  change String.Slice.Pattern.ForwardPattern.dropPrefix? prefixText.toSlice text.toSlice = none ↔
    ∀ tail, ¬ prefixText ++ tail = text at noPrefix
  classical
  rw [Option.isSome_iff_ne_none]
  constructor
  · intro found
    apply Classical.byContradiction
    intro noTail
    apply found
    apply noPrefix.mpr
    intro tail equal
    exact noTail ⟨tail, equal.symm⟩
  · rintro ⟨tail, equal⟩ missing
    exact (noPrefix.mp missing) tail equal.symm

theorem encode_not_prefixed (bytes : ByteArray) : (encode bytes).startsWith "0x" = false := by
  apply Bool.eq_false_iff.mpr
  intro hasPrefix
  obtain ⟨tail, equal⟩ := (startsWith_iff_append (encode bytes) "0x" (by decide )).mp hasPrefix
  have lexical := encode_lexical bytes
  rw [equal, String.toList_append, List.all_append] at lexical
  have invalid : "0x".toList.all lowerHex = false := by decide
  rw [invalid] at lexical
  simp at lexical

theorem prefixed_startsWith (text : String) : ("0x" ++ text).startsWith "0x" = true :=
  (startsWith_iff_append _ _ (by decide)).mpr ⟨text, rfl⟩

theorem decode_encode (bytes : ByteArray) : decode (encode bytes) = .ok bytes := by
  unfold decode
  rw [encode_not_prefixed]
  simp only [Bool.false_eq_true, ↓reduceIte, encode, String.toList_ofList]
  rw [decodeChars_encodeList]

theorem decode_prefixed_encode (bytes : ByteArray) : decode ("0x" ++ encode bytes) = .ok bytes := by
  unfold decode
  rw [prefixed_startsWith]
  simp only [↓reduceIte, String.toList_append]
  have strip : List.drop 2 ("0x".toList ++ (encode bytes).toList) = (encode bytes).toList := by rfl
  rw [strip]
  simpa only [decode, encode_not_prefixed, Bool.false_eq_true, ↓reduceIte] using decode_encode bytes

theorem encodeList_high (bytes : List UInt8) (index : Nat) (inside : index < bytes.length) :
    (encodeList bytes)[2 * index]! = digits[bytes[index]!.toNat / 16]! := by
  induction bytes generalizing index with
  | nil => simp at inside
  | cons byte rest ih =>
    cases index with
    | zero => rfl
    | succ index =>
      have shifted : 2 * (index + 1) = (2 * index + 1) + 1 := by omega
      simp only [encodeList, List.flatMap_cons, byteChars, List.cons_append, shifted,
        List.getElem!_cons_succ]
      exact ih index (by simpa using inside)

theorem encodeList_low (bytes : List UInt8) (index : Nat) (inside : index < bytes.length) :
    (encodeList bytes)[2 * index + 1]! = digits[bytes[index]!.toNat % 16]! := by
  induction bytes generalizing index with
  | nil => simp at inside
  | cons byte rest ih =>
    cases index with
    | zero => rfl
    | succ index =>
      have shifted : 2 * (index + 1) + 1 = ((2 * index + 1) + 1) + 1 := by omega
      simp only [encodeList, List.flatMap_cons, byteChars, List.cons_append, shifted,
        List.getElem!_cons_succ]
      exact ih index (by simpa using inside)

theorem byte_nibbles (byte : UInt8) :
    nibble (digits[byte.toNat / 16]!) = some (byte.toNat / 16) ∧
    nibble (digits[byte.toNat % 16]!) = some (byte.toNat % 16) ∧
    UInt8.ofNat ((byte.toNat / 16) * 16 + byte.toNat % 16) = byte := by
  have finite : ∀ value : Fin 256,
      nibble (digits[value.val / 16]!) = some (value.val / 16) ∧
      nibble (digits[value.val % 16]!) = some (value.val % 16) ∧
      UInt8.ofNat ((value.val / 16) * 16 + value.val % 16) = UInt8.ofNat value.val := by decide
  simpa only [UInt8.toNat_ofNat_of_lt' byte.toNat_lt_size, UInt8.ofNat_toNat] using
    finite ⟨byte.toNat, byte.toNat_lt_size⟩

end LeanCrypto.Hex
#print axioms LeanCrypto.Hex.byte_pair_inverse

#print axioms LeanCrypto.Hex.encodeList_fold

#print axioms LeanCrypto.Hex.byte_chars_lexical
#print axioms LeanCrypto.Hex.encodeList_length
#print axioms LeanCrypto.Hex.encodeList_lexical
#print axioms LeanCrypto.Hex.encodeList_lower
#print axioms LeanCrypto.Hex.encode_length
#print axioms LeanCrypto.Hex.encode_lexical
#print axioms LeanCrypto.Hex.encode_lower

#print axioms LeanCrypto.Hex.decodeList_encodeList

#print axioms LeanCrypto.Hex.decodeLoop_reference

#print axioms LeanCrypto.Hex.decodeChars_encodeList
#print axioms LeanCrypto.Hex.startsWith_iff_append

#print axioms LeanCrypto.Hex.encode_not_prefixed
#print axioms LeanCrypto.Hex.prefixed_startsWith
#print axioms LeanCrypto.Hex.decode_encode
#print axioms LeanCrypto.Hex.decode_prefixed_encode

#print axioms LeanCrypto.Hex.encodeList_high
#print axioms LeanCrypto.Hex.encodeList_low

#print axioms LeanCrypto.Hex.byte_nibbles
