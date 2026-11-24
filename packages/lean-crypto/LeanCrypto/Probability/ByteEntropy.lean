import LeanCrypto.FixedBytes
import LeanCrypto.Probability.Rejection

/-!
An explicit finite alphabet of independent uniform UInt8 coordinates.
The sums below enumerate bytes before calling the runtime decoder; the
change-of-variables theorem is proved from that decoder's bijection. This
is conditional on uniform independent source bytes and makes no claim
about the kernel entropy implementation or Groth16 zero knowledge.
-/
namespace LeanCrypto.Probability.ByteEntropy

open LeanCrypto.FixedBytes
open LeanCrypto.Sampling
open LeanCrypto.Probability.Rejection

/-- Enumerate every possible actual byte at each position with weight one. -/
def sumLists : Nat → (List UInt8 → Nat) → Nat
  | 0, event => event []
  | width + 1, event =>
      sumTo 256 (fun byte => sumLists width (fun rest => event (UInt8.ofNat byte :: rest)))

theorem sumLists_congr (width : Nat) (left right : List UInt8 → Nat)
    (equal : ∀ bytes, bytes.length = width → left bytes = right bytes) :
    sumLists width left = sumLists width right := by
  induction width generalizing left right with
  | zero => exact equal [] rfl
  | succ width ih =>
    apply sumTo_congr
    intro byte _
    apply ih
    intro rest length
    exact equal _ (by simp only [List.length_cons, length])

/-- Lexicographic blocks partition a finite interval without duplicates. -/
theorem sumTo_mul (high low : Nat) (event : Nat → Nat) :
    sumTo (high * low) event =
      sumTo high (fun hi => sumTo low (fun lo => event (hi * low + lo))) := by
  induction high with
  | zero => simp only [Nat.zero_mul, sumTo]
  | succ high ih =>
    rw [Nat.add_mul, Nat.one_mul, sumTo_split, sumTo, ih]

/-- Weighted change of variables, derived by enumerating the byte product. -/
theorem sumLists_decode (width : Nat) (event : Nat → Nat) :
    sumLists width (fun bytes => event (decodeList bytes)) =
      sumTo (256 ^ width) event := by
  induction width generalizing event with
  | zero => simp [sumLists, sumTo, decodeList]
  | succ width ih =>
    simp only [sumLists]
    calc
      _ = sumTo 256 (fun byte => sumLists width
          (fun rest => event (byte * 256 ^ width + decodeList rest))) := by
        apply sumTo_congr
        intro byte bound
        apply sumLists_congr
        intro rest length
        simp only [decodeList, length]
        rw [UInt8.toNat_ofNat_of_lt' bound]
      _ = sumTo 256 (fun byte => sumTo (256 ^ width)
          (fun value => event (byte * 256 ^ width + value))) := by
        apply sumTo_congr
        intro byte _
        exact ih (fun value => event (byte * 256 ^ width + value))
      _ = sumTo (256 ^ (width + 1)) event := by
        rw [← sumTo_mul, Nat.pow_succ, Nat.mul_comm]

def sumBytes (width : Nat) (event : ByteArray → Nat) : Nat :=
  sumLists width (fun bytes => event ⟨bytes.toArray⟩)

theorem sumBytes_congr (width : Nat) (left right : ByteArray → Nat)
    (equal : ∀ bytes, bytes.size = width → left bytes = right bytes) :
    sumBytes width left = sumBytes width right := by
  apply sumLists_congr
  intro bytes length
  apply equal
  simpa only [ByteArray.size, List.size_toArray] using length

theorem sumBytes_decode (width : Nat) (event : Nat → Nat) :
    sumBytes width (fun bytes => event (decode bytes)) =
      sumTo (256 ^ width) event := by
  simpa only [sumBytes, decode, List.toList_toArray] using sumLists_decode width event

theorem sumBytes_total (width : Nat) : sumBytes width (fun _ => 1) = 256 ^ width := by
  have h := sumBytes_decode width (fun _ => 1)
  simpa only [sumTo_const, Nat.mul_one] using h

theorem sumBytes_uniform (width value : Nat) :
    sumBytes width (fun bytes => if decode bytes = value then 1 else 0) =
      if value < 256 ^ width then 1 else 0 := by
  rw [sumBytes_decode width (fun actual => if actual = value then 1 else 0), sumTo_delta]

/-- Exact equality to the decoder currently used by the IO sampler. -/
theorem runtime_decoder (bytes : ByteArray) : bigEndianNat bytes = decode bytes :=
  (decode_eq_foldl bytes).symm

theorem uint256_radix : 256 ^ 32 = 2 ^ 256 := by decide

theorem runtime_decoder_bound (bytes : ByteArray) (width : bytes.size = 32) :
    bigEndianNat bytes < 2 ^ 256 := by
  rw [runtime_decoder]
  simpa only [width, uint256_radix] using decode_lt bytes

/-- Every uint256 has exactly one full-width 32-byte runtime encoding. -/
theorem runtime_uint256_bijection (value : Fin (2 ^ 256)) :
    ∃ bytes : Bytes 32, bigEndianNat bytes.val = value.val ∧
      ∀ other : Bytes 32, bigEndianNat other.val = value.val → other = bytes := by
  have bound : value.val < 256 ^ 32 := by simpa only [uint256_radix] using value.isLt
  let bytes : Bytes 32 := ⟨encode 32 value.val, encode_size 32 value.val⟩
  refine ⟨bytes, ?_, ?_⟩
  · rw [runtime_decoder]
    exact decode_encode 32 value.val bound
  · intro other equal
    apply decode_injective
    rw [← runtime_decoder, equal]
    exact (decode_encode 32 value.val bound).symm

theorem runtime_candidate (bytes : ByteArray) (width : bytes.size = 32) :
    (admitCandidate bytes).map (fun result => result.map (fun scalar => scalar.value)) =
      .ok (candidate LeanCrypto.bn254ScalarPrime (decode bytes)) := by
  simp only [admitCandidate, width, if_pos, Except.map]
  rw [runtime_candidate_matches, runtime_decoder]

/-- Exact first-draw law for the actual malformed-width-checking runtime
classifier, with Scalar proof fields erased only after classification. -/
theorem runtime_candidate_sum (event : Option Nat → Nat) :
    sumBytes 32 (fun bytes => match
      (admitCandidate bytes).map (fun result => result.map (fun scalar => scalar.value)) with
      | .error _ => 0
      | .ok result => event result) =
      sumTo (2 ^ 256) (fun value =>
        event (candidate LeanCrypto.bn254ScalarPrime value)) := by
  calc
    _ = sumBytes 32 (fun bytes =>
        event (candidate LeanCrypto.bn254ScalarPrime (decode bytes))) := by
      apply sumBytes_congr
      intro bytes width
      rw [runtime_candidate bytes width]
    _ = _ := by
      rw [sumBytes_decode 32 (fun value =>
        event (candidate LeanCrypto.bn254ScalarPrime value)), uint256_radix]

/-- Each draw enumerates the actual byte product, then calls the runtime
fold decoder. Terminal observations count the independent unread suffix. -/
def byteCount (width : Nat) : Nat → DrawTree α → (Option α → Nat) → Nat
  | n, .done value, event => (256 ^ width) ^ n * event (some value)
  | n, .abort, event => (256 ^ width) ^ n * event none
  | 0, .draw _, _ => 0
  | n + 1, .draw branch, event =>
      sumBytes width (fun bytes => byteCount width n (branch (bigEndianNat bytes)) event)

/-- Transfer every event of every lazy observation tree from bytes to the
existing finite-value model, including early returns and sequential binds. -/
theorem byteCount_eq_count (width budget : Nat) (tree : DrawTree α)
    (event : Option α → Nat) :
    byteCount width budget tree event = DrawTree.count (256 ^ width) budget tree event := by
  induction budget generalizing tree with
  | zero => cases tree <;> rfl
  | succ budget ih =>
    cases tree with
    | done _ => rfl
    | abort => rfl
    | draw branch =>
      simp only [byteCount, DrawTree.count]
      calc
        _ = sumBytes width (fun bytes =>
            DrawTree.count (256 ^ width) budget (branch (decode bytes)) event) := by
          apply sumBytes_congr
          intro bytes _
          rw [ih, runtime_decoder]
        _ = _ := sumBytes_decode width (fun value =>
          DrawTree.count (256 ^ width) budget (branch value) event)

/-- Production transfer for arbitrary result types, so this also applies to
sequential pair trees and all their joint events. -/
theorem bytes32_count (budget : Nat) (tree : DrawTree α) (event : Option α → Nat) :
    byteCount 32 budget tree event = DrawTree.count (2 ^ 256) budget tree event := by
  rw [byteCount_eq_count, uint256_radix]

def byteMass (width q budget : Nat) (event : Option Nat → Nat) : Nat :=
  byteCount width budget (sampler q budget) event

theorem byteMass_eq_mass (width q budget : Nat) (event : Option Nat → Nat) :
    byteMass width q budget event = mass (256 ^ width) q budget event :=
  byteCount_eq_count width budget (sampler q budget) event

theorem bytes32_mass (q budget : Nat) (event : Option Nat → Nat) :
    byteMass 32 q budget event = mass (2 ^ 256) q budget event := by
  rw [byteMass_eq_mass, uint256_radix]

/-- Conditional uniformity transferred from independent uniform source bytes,
with exact integer counts and the existing shared runtime retry program. -/
theorem bytes32_conditional_uniform (q budget value : Nat)
    (positive : 0 < q) (fits : q ≤ 2 ^ 256) (allowed : admissible q value = true) :
    byteMass 32 q budget (valueEvent value) * (q - 1) =
      byteMass 32 q budget successEvent := by
  rw [bytes32_mass, bytes32_mass]
  exact conditional_uniform (2 ^ 256) q budget value positive fits allowed

end LeanCrypto.Probability.ByteEntropy

#print axioms LeanCrypto.Probability.ByteEntropy.sumLists_congr
#print axioms LeanCrypto.Probability.ByteEntropy.sumTo_mul
#print axioms LeanCrypto.Probability.ByteEntropy.sumLists_decode
#print axioms LeanCrypto.Probability.ByteEntropy.sumBytes_congr
#print axioms LeanCrypto.Probability.ByteEntropy.sumBytes_decode
#print axioms LeanCrypto.Probability.ByteEntropy.sumBytes_total
#print axioms LeanCrypto.Probability.ByteEntropy.sumBytes_uniform
#print axioms LeanCrypto.Probability.ByteEntropy.runtime_decoder
#print axioms LeanCrypto.Probability.ByteEntropy.uint256_radix
#print axioms LeanCrypto.Probability.ByteEntropy.runtime_decoder_bound
#print axioms LeanCrypto.Probability.ByteEntropy.runtime_uint256_bijection
#print axioms LeanCrypto.Probability.ByteEntropy.runtime_candidate
#print axioms LeanCrypto.Probability.ByteEntropy.runtime_candidate_sum
#print axioms LeanCrypto.Probability.ByteEntropy.byteCount_eq_count
#print axioms LeanCrypto.Probability.ByteEntropy.bytes32_count
#print axioms LeanCrypto.Probability.ByteEntropy.byteMass_eq_mass
#print axioms LeanCrypto.Probability.ByteEntropy.bytes32_mass
#print axioms LeanCrypto.Probability.ByteEntropy.bytes32_conditional_uniform
