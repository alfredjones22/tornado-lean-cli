import Std

/-! Fixed-width big-endian bytes. Leading zero bytes are retained. -/
namespace LeanCrypto.FixedBytes

def decodeList : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat * 256 ^ rest.length + decodeList rest

def encodeList : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value =>
      UInt8.ofNat (value / 256 ^ width) :: encodeList width (value % 256 ^ width)

theorem encodeList_length (width value : Nat) :
    (encodeList width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp only [encodeList, List.length_cons, ih]

theorem decodeList_lt (bytes : List UInt8) :
    decodeList bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [decodeList]
  | cons byte rest ih =>
    simp only [decodeList, List.length_cons, Nat.pow_succ]
    have hb : byte.toNat < 256 := byte.toNat_lt_size
    have hp : 0 < 256 ^ rest.length := Nat.pow_pos (by decide)
    calc
      byte.toNat * 256 ^ rest.length + decodeList rest
          < byte.toNat * 256 ^ rest.length + 256 ^ rest.length := Nat.add_lt_add_left ih _
      _ = (byte.toNat + 1) * 256 ^ rest.length := by rw [Nat.add_mul]; simp
      _ ≤ 256 * 256 ^ rest.length := Nat.mul_le_mul_right _ (by omega)
      _ = _ := Nat.mul_comm _ _

theorem decodeList_encodeList (width value : Nat) (bound : value < 256 ^ width) :
    decodeList (encodeList width value) = value := by
  induction width generalizing value with
  | zero =>
    have hz : value = 0 := by simpa using bound
    subst value
    rfl
  | succ width ih =>
    have hp : 0 < 256 ^ width := Nat.pow_pos (by decide)
    have quotient : value / 256 ^ width < 256 := by
      apply (Nat.div_lt_iff_lt_mul hp).2
      simpa [Nat.pow_succ, Nat.mul_comm] using bound
    simp only [encodeList, decodeList, encodeList_length]
    rw [UInt8.toNat_ofNat_of_lt' quotient, ih _ (Nat.mod_lt _ hp)]
    simpa [Nat.mul_comm] using Nat.div_add_mod value (256 ^ width)

theorem encodeList_decodeList (bytes : List UInt8) :
    encodeList bytes.length (decodeList bytes) = bytes := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have hp : 0 < 256 ^ rest.length := Nat.pow_pos (by decide)
    have hr := decodeList_lt rest
    have divide : (byte.toNat * 256 ^ rest.length + decodeList rest) / 256 ^ rest.length =
        byte.toNat := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add]
    have modulo : (byte.toNat * 256 ^ rest.length + decodeList rest) % 256 ^ rest.length =
        decodeList rest := by simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
    simp only [List.length_cons, decodeList, encodeList, divide, modulo]
    rw [UInt8.ofNat_toNat, ih]

theorem foldl_decodeList (bytes : List UInt8) (initial : Nat) :
    bytes.foldl (fun value byte => value * 256 + byte.toNat) initial =
      initial * 256 ^ bytes.length + decodeList bytes := by
  induction bytes generalizing initial with
  | nil => simp [decodeList]
  | cons byte rest ih =>
    simp only [List.foldl_cons, ih, List.length_cons, decodeList, Nat.pow_succ]
    simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

def decode (bytes : ByteArray) : Nat := decodeList bytes.data.toList

def encode (width value : Nat) : ByteArray := ⟨(encodeList width value).toArray⟩

theorem encode_size (width value : Nat) : (encode width value).size = width := by
  simp [encode, ByteArray.size, encodeList_length]

theorem decode_lt (bytes : ByteArray) : decode bytes < 256 ^ bytes.size := by
  change decodeList bytes.data.toList < 256 ^ bytes.data.size
  have h := decodeList_lt bytes.data.toList
  simpa only [Array.length_toList] using h

theorem decode_encode (width value : Nat) (bound : value < 256 ^ width) :
    decode (encode width value) = value := by
  simpa [decode, encode] using decodeList_encodeList width value bound

theorem encode_decode (bytes : ByteArray) : encode bytes.size (decode bytes) = bytes := by
  cases bytes with
  | mk data =>
    simp only [encode, decode, ByteArray.size]
    have h := encodeList_decodeList data.toList
    simpa using congrArg (fun xs : List UInt8 => ByteArray.mk xs.toArray) h

theorem decode_eq_foldl (bytes : ByteArray) :
    decode bytes = bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0 := by
  rw [← Array.foldl_toList, foldl_decodeList]
  simp [decode]

abbrev Bytes (width : Nat) := { bytes : ByteArray // bytes.size = width }

def toNat (bytes : Bytes width) : Fin (256 ^ width) :=
  ⟨decode bytes.val, by simpa [bytes.property] using decode_lt bytes.val⟩

def ofNat (value : Fin (256 ^ width)) : Bytes width :=
  ⟨encode width value.val, encode_size width value.val⟩

theorem toNat_ofNat (value : Fin (256 ^ width)) : toNat (ofNat value) = value := by
  apply Fin.ext
  exact decode_encode width value.val value.isLt

theorem ofNat_toNat (bytes : Bytes width) : ofNat (toNat bytes) = bytes := by
  apply Subtype.ext
  change encode width (decode bytes.val) = bytes.val
  simpa only [bytes.property] using encode_decode bytes.val

theorem decode_injective (left right : Bytes width) (equal : decode left.val = decode right.val) :
    left = right := by
  apply Subtype.ext
  calc
    left.val = encode width (decode left.val) := by simpa only [left.property] using (encode_decode left.val).symm
    _ = encode width (decode right.val) := congrArg (encode width) equal
    _ = right.val := by simpa only [right.property] using encode_decode right.val

end LeanCrypto.FixedBytes

#print axioms LeanCrypto.FixedBytes.encodeList_length
#print axioms LeanCrypto.FixedBytes.decodeList_lt
#print axioms LeanCrypto.FixedBytes.decodeList_encodeList
#print axioms LeanCrypto.FixedBytes.encodeList_decodeList
#print axioms LeanCrypto.FixedBytes.foldl_decodeList
#print axioms LeanCrypto.FixedBytes.encode_size
#print axioms LeanCrypto.FixedBytes.decode_lt
#print axioms LeanCrypto.FixedBytes.decode_encode
#print axioms LeanCrypto.FixedBytes.encode_decode
#print axioms LeanCrypto.FixedBytes.decode_eq_foldl
#print axioms LeanCrypto.FixedBytes.toNat_ofNat
#print axioms LeanCrypto.FixedBytes.ofNat_toNat
#print axioms LeanCrypto.FixedBytes.decode_injective
