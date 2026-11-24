import LeanCrypto.Groth16.MSM
import LeanCrypto.FixedBytes
import LeanCrypto.HexWord
import Mathlib.Tactic.NormNum

/-! Proof references mirror the actual private serializer word loop. The
public solidityProofBytes connection is by kernel definitional equality. -/
set_option autoImplicit false

namespace LeanCrypto.Proofs.Groth16Codec

open LeanCrypto.BN254 LeanCrypto.Groth16

/-- Literal copy of the actual private MSM uintWord helper. -/
def wordProgram (value : Nat) : Except String ByteArray := do
  if value >= 2 ^ 256 then throw "ABI uint256 is out of range."
  let mut result := ByteArray.empty
  for i in [0:32] do
    result := result.push ((value / 2 ^ (8 * (32 - 1 - i)) % 256).toUInt8)
  return result

def wordList : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, value => wordList width (value / 256) ++ [UInt8.ofNat (value % 256)]

theorem wordList_positional (width value : Nat) :
    wordList width value = (List.range width).map (fun index =>
      UInt8.ofNat (value / 256 ^ (width - 1 - index) % 256)) := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih =>
    rw [wordList, ih, List.range_succ, List.map_append]
    simp only [List.map_singleton, Nat.add_sub_cancel, Nat.sub_self, Nat.pow_zero, Nat.div_one]
    congr 1
    apply List.map_congr_left
    intro index member
    have bound : index < width := List.mem_range.mp member
    have exponent : width - index = (width - 1 - index) + 1 := by omega
    rw [Nat.div_div_eq_div_mul, exponent, Nat.pow_succ]
    simp only [Nat.mul_comm]

theorem wordList_length (width value : Nat) : (wordList width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [wordList, ih]

theorem wordList_inverse (width value : Nat) (bound : value < 256 ^ width) :
    LeanCrypto.FixedBytes.decodeList (wordList width value) = value := by
  induction width generalizing value with
  | zero =>
    have zero : value = 0 := by simpa using bound
    subst value
    rfl
  | succ width ih =>
    have quotient : value / 256 < 256 ^ width := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
      simpa only [Nat.pow_succ] using bound
    rw [wordList, LeanCrypto.Hex.decodeList_append_byte, ih _ quotient,
      UInt8.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide : 0 < 256))]
    exact Nat.div_add_mod' value 256

theorem wordList_fixed (width value : Nat) (bound : value < 256 ^ width) :
    wordList width value = LeanCrypto.FixedBytes.encodeList width value := by
  have inverse := LeanCrypto.FixedBytes.encodeList_decodeList (wordList width value)
  rw [wordList_length, wordList_inverse width value bound] at inverse
  exact inverse.symm

def appendLoop (indices : List Nat) (valueAt : Nat → UInt8) (initial : ByteArray) :
    Except String ByteArray :=
  forIn indices initial (fun i current => pure (.yield (current.push (valueAt i))))

theorem appendLoop_list (indices : List Nat) (valueAt : Nat → UInt8) (initial : ByteArray) :
    appendLoop indices valueAt initial =
      .ok ⟨(initial.data.toList ++ indices.map valueAt).toArray⟩ := by
  induction indices generalizing initial with
  | nil => simp [appendLoop, pure, Except.pure]
  | cons head rest ih =>
    simp only [appendLoop, List.forIn_cons, pure, Except.pure, bind, Except.bind]
    change appendLoop rest valueAt (initial.push (valueAt head)) = _
    rw [ih]
    congr 1
    simp [ByteArray.push, List.append_assoc]

theorem wordProgram_construct (value : Nat) (bound : value < 2 ^ 256) :
    wordProgram value = .ok (LeanCrypto.FixedBytes.encode 32 value) := by
  have bitBytes : ∀ n : Nat, 2 ^ (8 * n) = 256 ^ n := by
    intro n
    rw [Nat.pow_mul]
  have bytesBound : value < 256 ^ 32 := by simpa using bound
  simp only [wordProgram, Nat.not_le_of_lt bound, ↓reduceIte,
    bind, Except.bind, pure, Except.pure]
  change (forIn (Std.Legacy.Range.mk 0 32 1 (by decide)) ByteArray.empty
    (fun i current => (pure (ForInStep.yield (current.push
      ((value / 2 ^ (8 * (32 - 1 - i)) % 256).toUInt8))) : Except String (ForInStep ByteArray))) >>= pure) = _
  rw [bind_pure, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [← List.range_eq_range']
  change appendLoop (List.range 32) (fun i =>
    UInt8.ofNat (value / 2 ^ (8 * (32 - 1 - i)) % 256)) ByteArray.empty = _
  rw [appendLoop_list]
  simp only [ByteArray.empty]
  simp_rw [bitBytes]
  rw [← wordList_positional, wordList_fixed 32 value bytesBound]
  rfl

def affineLimbs (a : G1.Affine) (b : G2.Affine) (c : G1.Affine) : List Nat :=
  [a.x.val, a.y.val, b.x.c1.val, b.x.c0.val, b.y.c1.val, b.y.c0.val, c.x.val, c.y.val]

def wordsProgram (a : G1.Affine) (b : G2.Affine) (c : G1.Affine) : Except String ByteArray := do
  return (← wordProgram a.x.val) ++ (← wordProgram a.y.val) ++
    (← wordProgram b.x.c1.val) ++ (← wordProgram b.x.c0.val) ++
    (← wordProgram b.y.c1.val) ++ (← wordProgram b.y.c0.val) ++
    (← wordProgram c.x.val) ++ (← wordProgram c.y.val)

/-- This is a definitional connection to the actual public serializer and
its private word helper. The three hypotheses are explicit admitted affine
normalization outputs; no G2 normalization theorem is claimed here. -/
theorem solidityProofBytes_affine_outputs (proof : Types.ProofPoints)
    (a : G1.Affine) (b : G2.Affine) (c : G1.Affine)
    (aOutput : proof.piA.toAffine = .ok (some a))
    (bOutput : proof.piB.toAffine = .ok (some b))
    (cOutput : proof.piC.toAffine = .ok (some c)) :
    MSM.solidityProofBytes proof = wordsProgram a b c := by
  simp only [MSM.solidityProofBytes, aOutput, bOutput, cOutput, bind, Except.bind]
  rfl

def encodeWords (words : List Nat) : List UInt8 :=
  words.flatMap (LeanCrypto.FixedBytes.encodeList 32)

def decodeWords : Nat → List UInt8 → List Nat
  | 0, _ => []
  | count + 1, bytes => LeanCrypto.FixedBytes.decodeList (bytes.take 32) ::
    decodeWords count (bytes.drop 32)

theorem encodeWords_length (words : List Nat) : (encodeWords words).length = 32 * words.length := by
  induction words with
  | nil => rfl
  | cons value rest ih =>
    change ((LeanCrypto.FixedBytes.encodeList 32 value) ++ encodeWords rest).length = _
    rw [List.length_append, LeanCrypto.FixedBytes.encodeList_length, ih, List.length_cons]
    omega

theorem decodeWords_encodeWords (words : List Nat)
    (bounds : ∀ value, value ∈ words → value < 256 ^ 32) :
    decodeWords words.length (encodeWords words) = words := by
  induction words with
  | nil => rfl
  | cons value rest ih =>
    have headBound := bounds value (by simp)
    have tailBounds : ∀ n, n ∈ rest → n < 256 ^ 32 := fun n member => bounds n (by simp [member])
    have length := LeanCrypto.FixedBytes.encodeList_length 32 value
    simp only [List.length_cons, encodeWords, List.flatMap_cons, decodeWords]
    have take : (LeanCrypto.FixedBytes.encodeList 32 value ++ encodeWords rest).take 32 =
        LeanCrypto.FixedBytes.encodeList 32 value := List.take_left' length
    have drop : (LeanCrypto.FixedBytes.encodeList 32 value ++ encodeWords rest).drop 32 =
        encodeWords rest := List.drop_left' length
    change LeanCrypto.FixedBytes.decodeList ((LeanCrypto.FixedBytes.encodeList 32 value ++
      encodeWords rest).take 32) :: decodeWords rest.length
      ((LeanCrypto.FixedBytes.encodeList 32 value ++ encodeWords rest).drop 32) = _
    rw [take, drop, LeanCrypto.FixedBytes.decodeList_encodeList 32 value headBound]
    exact congrArg (List.cons value) (ih tailBounds)

theorem affine_limb_bounds (a : G1.Affine) (b : G2.Affine) (c : G1.Affine) :
    ∀ value, value ∈ affineLimbs a b c → value < 2 ^ 256 := by
  have primeBound : G1.basePrime < 2 ^ 256 := by decide
  intro value member
  simp only [affineLimbs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h <;> subst value
  · exact a.x.bounded.trans primeBound
  · exact a.y.bounded.trans primeBound
  · exact b.x.c1.bounded.trans primeBound
  · exact b.x.c0.bounded.trans primeBound
  · exact b.y.c1.bounded.trans primeBound
  · exact b.y.c0.bounded.trans primeBound
  · exact c.x.bounded.trans primeBound
  · exact c.y.bounded.trans primeBound

/-- Every limb is independently canonical, so no uint256 guard can fail. -/
theorem wordsProgram_construct (a : G1.Affine) (b : G2.Affine) (c : G1.Affine) :
    wordsProgram a b c = .ok ⟨(encodeWords (affineLimbs a b c)).toArray⟩ := by
  have limit : ∀ value : G1.Fp, value.val < 2 ^ 256 :=
    fun value => value.bounded.trans (by decide)
  simp only [wordsProgram, wordProgram_construct _ (limit _), bind, Except.bind, pure, Except.pure]
  apply congrArg (fun bytes : ByteArray => (Except.ok bytes : Except String ByteArray))
  apply ByteArray.ext
  simp [encodeWords, affineLimbs, LeanCrypto.FixedBytes.encode, ByteArray.data_append]

theorem solidityProofBytes_construct (proof : Types.ProofPoints)
    (a : G1.Affine) (b : G2.Affine) (c : G1.Affine)
    (aOutput : proof.piA.toAffine = .ok (some a))
    (bOutput : proof.piB.toAffine = .ok (some b))
    (cOutput : proof.piC.toAffine = .ok (some c)) :
    MSM.solidityProofBytes proof = .ok ⟨(encodeWords (affineLimbs a b c)).toArray⟩ := by
  rw [solidityProofBytes_affine_outputs proof a b c aOutput bOutput cOutput]
  exact wordsProgram_construct a b c

theorem solidityProofBytes_length (proof : Types.ProofPoints)
    (a : G1.Affine) (b : G2.Affine) (c : G1.Affine)
    (aOutput : proof.piA.toAffine = .ok (some a))
    (bOutput : proof.piB.toAffine = .ok (some b))
    (cOutput : proof.piC.toAffine = .ok (some c)) :
    ∃ bytes, MSM.solidityProofBytes proof = .ok bytes ∧ bytes.size = 256 := by
  refine ⟨_, solidityProofBytes_construct proof a b c aOutput bOutput cOutput, ?_⟩
  simp [ByteArray.size, encodeWords_length, affineLimbs]

theorem solidityProofBytes_roundtrip (proof : Types.ProofPoints)
    (a : G1.Affine) (b : G2.Affine) (c : G1.Affine)
    (aOutput : proof.piA.toAffine = .ok (some a))
    (bOutput : proof.piB.toAffine = .ok (some b))
    (cOutput : proof.piC.toAffine = .ok (some c)) :
    ∃ bytes, MSM.solidityProofBytes proof = .ok bytes ∧
      decodeWords 8 bytes.data.toList = affineLimbs a b c := by
  refine ⟨_, solidityProofBytes_construct proof a b c aOutput bOutput cOutput, ?_⟩
  change decodeWords 8 (encodeWords (affineLimbs a b c)) = _
  have bounds : ∀ value, value ∈ affineLimbs a b c → value < 256 ^ 32 := by
    simpa using affine_limb_bounds a b c
  exact decodeWords_encodeWords (affineLimbs a b c) bounds

/-- Equal ordered normalized limb lists give exactly the same proof bytes,
regardless of projective representatives or public-signal metadata. -/
theorem encoded_limb_independence (a a' : G1.Affine) (b b' : G2.Affine) (c c' : G1.Affine)
    (same : affineLimbs a b c = affineLimbs a' b' c') :
    wordsProgram a b c = wordsProgram a' b' c' := by
  rw [wordsProgram_construct, wordsProgram_construct, same]

theorem encoded_limb_injective (a a' : G1.Affine) (b b' : G2.Affine) (c c' : G1.Affine)
    (same : wordsProgram a b c = wordsProgram a' b' c') :
    affineLimbs a b c = affineLimbs a' b' c' := by
  rw [wordsProgram_construct, wordsProgram_construct] at same
  have arrays := congrArg ByteArray.data (Except.ok.inj same)
  have lists : encodeWords (affineLimbs a b c) = encodeWords (affineLimbs a' b' c') := by
    simpa using congrArg Array.toList arrays
  have bounds₁ : ∀ value, value ∈ affineLimbs a b c → value < 256 ^ 32 := by
    simpa using affine_limb_bounds a b c
  have bounds₂ : ∀ value, value ∈ affineLimbs a' b' c' → value < 256 ^ 32 := by
    simpa using affine_limb_bounds a' b' c'
  have first := decodeWords_encodeWords (affineLimbs a b c) bounds₁
  have second := decodeWords_encodeWords (affineLimbs a' b' c') bounds₂
  change decodeWords 8 _ = _ at first second
  have decoded := congrArg (decodeWords 8) lists
  rwa [first, second] at decoded

theorem solidityProofBytes_publicSignals_irrelevant (proof : Types.ProofPoints) (signals : Array Nat) :
    MSM.solidityProofBytes {proof with publicSignals := signals} = MSM.solidityProofBytes proof := by
  rfl

end LeanCrypto.Proofs.Groth16Codec

#print axioms LeanCrypto.Proofs.Groth16Codec.wordList_positional
#print axioms LeanCrypto.Proofs.Groth16Codec.wordList_length
#print axioms LeanCrypto.Proofs.Groth16Codec.wordList_inverse
#print axioms LeanCrypto.Proofs.Groth16Codec.wordList_fixed
#print axioms LeanCrypto.Proofs.Groth16Codec.appendLoop_list
#print axioms LeanCrypto.Proofs.Groth16Codec.wordProgram_construct
#print axioms LeanCrypto.Proofs.Groth16Codec.solidityProofBytes_affine_outputs
#print axioms LeanCrypto.Proofs.Groth16Codec.encodeWords_length
#print axioms LeanCrypto.Proofs.Groth16Codec.decodeWords_encodeWords
#print axioms LeanCrypto.Proofs.Groth16Codec.affine_limb_bounds
#print axioms LeanCrypto.Proofs.Groth16Codec.wordsProgram_construct
#print axioms LeanCrypto.Proofs.Groth16Codec.solidityProofBytes_construct
#print axioms LeanCrypto.Proofs.Groth16Codec.solidityProofBytes_length
#print axioms LeanCrypto.Proofs.Groth16Codec.solidityProofBytes_roundtrip
#print axioms LeanCrypto.Proofs.Groth16Codec.encoded_limb_independence
#print axioms LeanCrypto.Proofs.Groth16Codec.encoded_limb_injective
#print axioms LeanCrypto.Proofs.Groth16Codec.solidityProofBytes_publicSignals_irrelevant
