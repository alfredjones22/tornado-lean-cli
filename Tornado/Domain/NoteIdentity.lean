import Tornado.Domain.Notes
import Tornado.Crypto.Pedersen
import Tornado.Crypto.Keccak
import LeanCrypto.Hex
import LeanCrypto.HexWord
set_option linter.unusedSimpArgs false

/-!
Classic Tornado public note identifiers computed natively in Lean. The raw
62-byte note preimage is split into two 31-byte secret segments; the first
31 bytes yield the nullifier hash, while all 62 yield the commitment.
-/

namespace Tornado.Domain

structure NoteIdentity where
  commitment : String
  nullifierHash : String
  deriving Repr, BEq, Inhabited

private def hexNibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode ASCII hex without relying on Node or viem. An optional lowercase
    `0x` prefix is accepted. Odd length or non-hex input fails. -/
def parseHexBytes (raw : String) : Except String ByteArray := do
  let chars := (if raw.startsWith "0x" then raw.toList.drop 2 else raw.toList).toArray
  if chars.size % 2 != 0 then throw "Hex input has an odd number of digits."
  let mut bytes := ByteArray.empty
  for index in [0:chars.size / 2] do
    let some hi := hexNibble chars[index * 2]!
      | throw "Hex input contains a non-hex digit."
    let some lo := hexNibble chars[index * 2 + 1]!
      | throw "Hex input contains a non-hex digit."
    bytes := bytes.push (UInt8.ofNat (hi * 16 + lo))
  return bytes

private def hexChar (value : Nat) : Char :=
  ("0123456789abcdef".toList[value]?).getD '0'

/-- Encode a bounded natural number as exactly 32 big-endian bytes with `0x`. -/
def toHex32 (value : Nat) : Except String String := do
  if value >= 2 ^ 256 then throw "Value does not fit in bytes32."
  let digits := (List.range 64).map fun index =>
    hexChar ((value / (16 ^ (63 - index))) % 16)
  return "0x" ++ String.ofList digits

def noteIdentity (note : ParsedNote) : Except String NoteIdentity := do
  if note.preimage.length != 124 then throw "Classic note preimage must contain 62 bytes."
  let bytes ← parseHexBytes note.preimage
  if bytes.size != 62 then throw "Classic note preimage must contain 62 bytes."
  let commitmentX ← Tornado.Crypto.pedersenX bytes
  let nullifierX ← Tornado.Crypto.pedersenX (bytes.extract 0 31)
  return { commitment := (← toHex32 commitmentX), nullifierHash := (← toHex32 nullifierX) }

theorem hexNibble_eq (char : Char) : hexNibble char = LeanCrypto.Hex.nibble char := by rfl

private def parseEncodedPairs (source : List UInt8) (indices : List Nat) (initial : ByteArray) :
    Except String ByteArray := do
  let chars := (LeanCrypto.Hex.encodeList source).toArray
  let mut bytes := initial
  for index in indices do
    let some hi := hexNibble chars[index * 2]! | throw "Hex input contains a non-hex digit."
    let some lo := hexNibble chars[index * 2 + 1]! | throw "Hex input contains a non-hex digit."
    bytes := bytes.push (UInt8.ofNat (hi * 16 + lo))
  return bytes

theorem parseEncodedPairs_construct (source : List UInt8) (indices : List Nat)
    (inside : ∀ index ∈ indices, index < source.length) (initial : ByteArray) :
    parseEncodedPairs source indices initial =
      .ok (initial ++ ByteArray.mk ((indices.map (fun index => source[index]!)).toArray)) := by
  induction indices generalizing initial with
  | nil =>
    simp only [parseEncodedPairs, List.forIn_nil, bind, Except.bind, pure, Except.pure,
      List.map_nil ]
    congr 1
    apply ByteArray.ext
    simp [ByteArray.data_append]
  | cons first rest ih =>
    have bound := inside first (by simp)
    have high : hexNibble ((LeanCrypto.Hex.encodeList source).toArray[first * 2]!) =
        some (source[first]!.toNat / 16) := by
      rw [List.getElem!_toArray, show first * 2 = 2 * first by omega,
        LeanCrypto.Hex.encodeList_high source first bound, hexNibble_eq]
      exact (LeanCrypto.Hex.byte_nibbles source[first]!).1
    have low : hexNibble ((LeanCrypto.Hex.encodeList source).toArray[first * 2 + 1]!) =
        some (source[first]!.toNat % 16) := by
      rw [List.getElem!_toArray, show first * 2 = 2 * first by omega,
        LeanCrypto.Hex.encodeList_low source first bound, hexNibble_eq]
      exact (LeanCrypto.Hex.byte_nibbles source[first]!).2.1
    have recover := (LeanCrypto.Hex.byte_nibbles source[first]!).2.2
    simp only [parseEncodedPairs, List.forIn_cons]
    rw [high]
    simp only [bind, Except.bind]
    rw [low]
    simp only [bind, Except.bind, pure, Except.pure, recover]
    change parseEncodedPairs source rest (initial.push source[first]!) = _
    rw [ih (fun index member => inside index (by simp [member]))]
    congr 1
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp [ByteArray.data_append, ByteArray.data_push, List.append_assoc]


theorem list_range_get (source : List α) [Inhabited α] :
    (List.range source.length).map (fun index => source[index]!) = source := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem right]

theorem parseHexBytes_hexEncode (bytes : ByteArray) :
    parseHexBytes (LeanCrypto.Hex.encode bytes) = .ok bytes := by
  unfold parseHexBytes
  rw [LeanCrypto.Hex.encode_not_prefixed]
  simp only [Bool.false_eq_true, ↓reduceIte, LeanCrypto.Hex.encode, String.toList_ofList]
  have even : (LeanCrypto.Hex.encodeList bytes.data.toList).toArray.size % 2 = 0 := by
    simp only [List.size_toArray, LeanCrypto.Hex.encodeList_length, Nat.mul_mod_right]
  rw [even]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← List.range_eq_range']
  rw [List.size_toArray, LeanCrypto.Hex.encodeList_length, Nat.mul_div_right _ (by decide : 0 < 2)]
  change parseEncodedPairs bytes.data.toList (List.range bytes.data.toList.length) ByteArray.empty = .ok bytes
  rw [parseEncodedPairs_construct _ _ (fun index member => List.mem_range.mp member), list_range_get]
  congr 1

theorem bytesToHex_eq_hexEncode (bytes : ByteArray) :
    Tornado.Crypto.bytesToHex bytes = LeanCrypto.Hex.encode bytes := by
  change (forIn bytes.data "" (fun byte acc => pure (.yield
    ((acc.push (LeanCrypto.Hex.digits[byte.toNat / 16]!)).push
      (LeanCrypto.Hex.digits[byte.toNat % 16]!)))) : Id String).run = _
  rw [Array.forIn_pure_yield_eq_foldl]
  change bytes.data.foldl (fun acc byte =>
    (acc.push (LeanCrypto.Hex.digits[byte.toNat / 16]!)).push
      (LeanCrypto.Hex.digits[byte.toNat % 16]!)) "" = _
  rw [← Array.foldl_toList, LeanCrypto.Hex.encodeList_fold]
  simp [LeanCrypto.Hex.encode]

theorem parseHexBytes_add_prefix (text : String) (unprefixed : text.startsWith "0x" = false) :
    parseHexBytes ("0x" ++ text) = parseHexBytes text := by
  unfold parseHexBytes
  rw [LeanCrypto.Hex.prefixed_startsWith, unprefixed]
  simp only [↓reduceIte, Bool.false_eq_true, String.toList_append]
  rfl

theorem parseHexBytes_bytesToHex (bytes : ByteArray) :
    parseHexBytes (Tornado.Crypto.bytesToHex bytes) = .ok bytes := by
  rw [bytesToHex_eq_hexEncode]
  exact parseHexBytes_hexEncode bytes

theorem parseHexBytes_prefixed_bytesToHex (bytes : ByteArray) :
    parseHexBytes ("0x" ++ Tornado.Crypto.bytesToHex bytes) = .ok bytes := by
  rw [bytesToHex_eq_hexEncode, parseHexBytes_add_prefix _ (LeanCrypto.Hex.encode_not_prefixed bytes)]
  exact parseHexBytes_hexEncode bytes

theorem bytesToHex_length (bytes : ByteArray) :
    (Tornado.Crypto.bytesToHex bytes).length = 2 * bytes.size := by
  rw [bytesToHex_eq_hexEncode, LeanCrypto.Hex.encode_length]

theorem bytesToHex_lower (bytes : ByteArray) :
    (Tornado.Crypto.bytesToHex bytes).toLower = Tornado.Crypto.bytesToHex bytes := by
  rw [bytesToHex_eq_hexEncode, LeanCrypto.Hex.encode_lower]

theorem bytesToHex_lexical (bytes : ByteArray) :
    (Tornado.Crypto.bytesToHex bytes).toList.all LeanCrypto.Hex.lowerHex = true := by
  rw [bytesToHex_eq_hexEncode]
  exact LeanCrypto.Hex.encode_lexical bytes


theorem hexChar_eq_digit (value : Nat) (bound : value < 16) :
    hexChar value = LeanCrypto.Hex.digits[value]! := by
  have finite : ∀ index : Fin 16, hexChar index.val = LeanCrypto.Hex.digits[index.val]! := by decide
  exact finite ⟨value, bound⟩

theorem toHex32_fixed (value : Nat) (bound : value < 2 ^ 256) :
    toHex32 value = .ok ("0x" ++ LeanCrypto.Hex.encode (LeanCrypto.FixedBytes.encode 32 value)) := by
  unfold toHex32
  rw [if_neg (show ¬ value ≥ 2 ^ 256 by omega)]
  simp only [pure, Except.pure, bind, Except.bind]
  have chars : (List.range 64).map (fun index => hexChar ((value / (16 ^ (63 - index))) % 16)) =
      LeanCrypto.Hex.wordDigits 64 value := by
    rw [LeanCrypto.Hex.wordDigits_positional]
    apply List.map_congr_left
    intro index _
    exact hexChar_eq_digit _ (Nat.mod_lt _ (by decide))
  rw [chars]
  have radix : 256 ^ 32 = 2 ^ 256 := by decide
  have fits : value < 256 ^ 32 := by simpa only [radix] using bound
  have representation := LeanCrypto.Hex.wordDigits_fixed_bytes 32 value fits
  change LeanCrypto.Hex.wordDigits 64 value = _ at representation
  rw [representation]
  simp only [LeanCrypto.Hex.encode, LeanCrypto.FixedBytes.encode, List.toList_toArray]

theorem toHex32_success_bytes (value : Nat) (text : String) (encoded : toHex32 value = .ok text) :
    ∃ bytes : ByteArray, parseHexBytes text = .ok bytes ∧ bytes.size = 32 ∧
      LeanCrypto.FixedBytes.decode bytes = value ∧ text.length = 66 := by
  by_cases bound : value < 2 ^ 256
  · rw [toHex32_fixed value bound] at encoded
    have same : "0x" ++ LeanCrypto.Hex.encode (LeanCrypto.FixedBytes.encode 32 value) = text :=
      Except.ok.inj encoded
    subst text
    refine ⟨LeanCrypto.FixedBytes.encode 32 value, ?_, LeanCrypto.FixedBytes.encode_size 32 value, ?_, ?_⟩
    · rw [parseHexBytes_add_prefix _ (LeanCrypto.Hex.encode_not_prefixed _)]
      exact parseHexBytes_hexEncode _
    · apply LeanCrypto.FixedBytes.decode_encode
      simpa only [show 256 ^ 32 = 2 ^ 256 by decide] using bound
    · rw [String.length_append, LeanCrypto.Hex.encode_length, LeanCrypto.FixedBytes.encode_size]
      rfl
  · simp [toHex32, show value ≥ 2 ^ 256 by omega, bind, Except.bind] at encoded


end Tornado.Domain

#print axioms Tornado.Domain.hexNibble_eq
#print axioms Tornado.Domain.parseEncodedPairs_construct

#print axioms Tornado.Domain.list_range_get
#print axioms Tornado.Domain.parseHexBytes_hexEncode

#print axioms Tornado.Domain.bytesToHex_eq_hexEncode
#print axioms Tornado.Domain.parseHexBytes_add_prefix
#print axioms Tornado.Domain.parseHexBytes_bytesToHex
#print axioms Tornado.Domain.parseHexBytes_prefixed_bytesToHex
#print axioms Tornado.Domain.bytesToHex_length
#print axioms Tornado.Domain.bytesToHex_lower
#print axioms Tornado.Domain.bytesToHex_lexical

#print axioms Tornado.Domain.hexChar_eq_digit
#print axioms Tornado.Domain.toHex32_fixed
#print axioms Tornado.Domain.toHex32_success_bytes
