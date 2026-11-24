import LeanCryptoProofs.BabyJubjub.SignedWindows

open Lean Elab Term Meta
elab "actualPedersenNibble" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Pedersen `LeanCrypto.signedNibble)
elab "actualPedersenChunk" : term =>
  mkConstWithFreshMVarLevels (mkPrivateNameCore `LeanCrypto.Pedersen `LeanCrypto.chunkScalar)
elab "unfoldPedersenChunk" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic1 fun goal => goal.deltaTarget (· ==
    mkPrivateNameCore `LeanCrypto.Pedersen `LeanCrypto.chunkScalar)

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjubWindows

abbrev nativeNibble (digit : Nat) : Int := actualPedersenNibble digit
abbrev nativeChunk (bytes : ByteArray) : Nat := actualPedersenChunk bytes

def byteDigits : List UInt8 → List Int
  | [] => []
  | byte :: rest => nativeNibble (byte.toNat % 16) :: nativeNibble (byte.toNat / 16) :: byteDigits rest

def byteStep (frame : MProd Int Int) (byte : UInt8) : MProd Int Int :=
  let signed := frame.1 + nativeNibble (byte.toNat % 16) * frame.2
  let weight := frame.2 * 32
  let signed := signed + nativeNibble (byte.toNat / 16) * weight
  ⟨signed, weight * 32⟩

def signedReference (bytes : ByteArray) : Int := Id.run do
  let mut signed : Int := 0
  let mut weight : Int := 1
  for byte in bytes.data do
    let n := byte.toNat
    signed := signed + nativeNibble (n % 16) * weight
    weight := weight * 32
    signed := signed + nativeNibble (n / 16) * weight
    weight := weight * 32
  return signed

theorem nibble_bounds (digit : Nat) : 1 ≤ |nativeNibble digit| ∧ |nativeNibble digit| ≤ 8 := by
  have bound := Nat.mod_lt digit (by decide : 0 < 8)
  change 1 ≤ |if digit ≥ 8 then -((digit % 8 + 1 : Nat) : Int) else ((digit % 8 + 1 : Nat) : Int)| ∧
    |if digit ≥ 8 then -((digit % 8 + 1 : Nat) : Int) else ((digit % 8 + 1 : Nat) : Int)| ≤ 8
  by_cases negative : digit ≥ 8
  · simp only [if_pos negative, abs_neg, abs_of_nonneg (Int.natCast_nonneg _)]
    omega
  · simp only [if_neg negative, abs_of_nonneg (Int.natCast_nonneg _)]
    omega

theorem byteDigits_valid (bytes : List UInt8) : ValidDigits (byteDigits bytes) := by
  induction bytes with
  | nil => simp [ValidDigits, byteDigits]
  | cons byte rest ih =>
    intro digit member
    simp only [byteDigits, List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact nibble_bounds _
    · exact nibble_bounds _
    · exact ih digit member

theorem byteDigits_length (bytes : List UInt8) : (byteDigits bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih => simp only [byteDigits, List.length_cons, ih]; omega

theorem byteFold_value (bytes : List UInt8) (signed weight : Int) :
    (bytes.foldl byteStep ⟨signed, weight⟩).fst = signed + weight * windowValue (byteDigits bytes) := by
  induction bytes generalizing signed weight with
  | nil => simp [byteDigits, windowValue]
  | cons byte rest ih =>
    simp only [List.foldl_cons, byteStep]
    rw [ih]
    simp only [byteDigits, windowValue]
    ring

theorem signedReference_fold (bytes : ByteArray) :
    signedReference bytes = (bytes.data.toList.foldl byteStep ⟨0, 1⟩).fst := by
  unfold signedReference
  simp only [pure_bind, Array.forIn_pure_yield_eq_foldl]
  simp only [Id.run_pure, ← Array.foldl_toList]
  rfl

theorem signedReference_value (bytes : ByteArray) :
    signedReference bytes = windowValue (byteDigits bytes.data.toList) := by
  rw [signedReference_fold, byteFold_value]
  ring

theorem nativeChunk_reference (bytes : ByteArray) :
    nativeChunk bytes = canonicalScalar (signedReference bytes) := by
  unfold nativeChunk
  unfoldPedersenChunk
  unfold signedReference canonicalScalar
  simp only [pure_bind, Array.forIn_pure_yield_eq_foldl]
  simp only [Id.run_pure]
  split <;> rfl

theorem nativeChunk_value (bytes : ByteArray) :
    nativeChunk bytes = canonicalScalar (windowValue (byteDigits bytes.data.toList)) := by
  rw [nativeChunk_reference, signedReference_value]

theorem nativeChunk_bounds (bytes : ByteArray) (positive : 0 < bytes.size) (bounded : bytes.size ≤ 25) :
    0 < nativeChunk bytes ∧ nativeChunk bytes < LeanCrypto.Proofs.BabyJubjubPrimes.subgroupOrder := by
  rw [nativeChunk_value]
  have size : (byteDigits bytes.data.toList).length ≤ 50 := by
    rw [byteDigits_length]
    have : bytes.data.toList.length = bytes.size := rfl
    omega
  have notEmpty : byteDigits bytes.data.toList ≠ [] := by
    intro empty
    have length := byteDigits_length bytes.data.toList
    rw [empty] at length
    have : bytes.data.toList.length = bytes.size := rfl
    simp only [List.length_nil] at length
    omega
  cases digits : byteDigits bytes.data.toList with
  | nil => exact False.elim (notEmpty digits)
  | cons digit rest =>
    apply valid_chunk_scalar digit rest
    · rw [← digits]; exact byteDigits_valid _
    · simpa only [digits] using size

end LeanCrypto.Proofs.BabyJubjubWindows
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.nibble_bounds
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.byteDigits_valid
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.byteDigits_length
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.byteFold_value
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.signedReference_fold
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.signedReference_value
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.nativeChunk_reference
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.nativeChunk_value
#print axioms LeanCrypto.Proofs.BabyJubjubWindows.nativeChunk_bounds
