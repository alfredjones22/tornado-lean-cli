import LeanCryptoProofs.WindowedMSM.WindowedSource

set_option autoImplicit false

namespace LeanCrypto.Proofs.WindowedMSM

variable {G : Type} [AddCommMonoid G] [Inhabited G]

def weightedBuckets (buckets : Array G) (radix : Nat) : G :=
  ∑ digit ∈ Finset.range radix, digit • buckets[digit]!

theorem weightedBuckets_replicate (radix : Nat) :
    weightedBuckets (Array.replicate radix (0 : G)) radix = 0 := by
  apply Finset.sum_eq_zero
  intro digit member
  have bounded := Finset.mem_range.mp member
  simp [bounded]

theorem bucket_update_weighted (buckets : Array G) (radix digit : Nat) (point : G)
    (shape : buckets.size = radix) (bounded : digit < radix) :
    weightedBuckets (buckets.set! digit (buckets[digit]! + point)) radix =
      weightedBuckets buckets radix + digit • point := by
  have digitBound : digit < buckets.size := by omega
  have terms (index : Nat) (member : index ∈ Finset.range radix) :
      index • (buckets.set! digit (buckets[digit]! + point))[index]! =
        index • buckets[index]! + if index = digit then digit • point else 0 := by
    have indexBound : index < buckets.size := by have := Finset.mem_range.mp member; omega
    by_cases same : index = digit
    · subst index
      simp [digitBound]
    · simp [indexBound, Ne.symm same, same]
  unfold weightedBuckets
  rw [Finset.sum_congr rfl terms, Finset.sum_add_distrib]
  simp [Finset.mem_range.mpr bounded]

def fillPrefix (points : Array G) (scalars : Array Nat) (divisor radix length : Nat) : Array G :=
  (List.range length).foldl (fun buckets index =>
    let digit := scalars[index]! / divisor % radix
    if digit != 0 then buckets.set! digit (buckets[digit]! + points[index]!) else buckets)
    (Array.replicate radix 0)

theorem fillPrefix_succ (points : Array G) (scalars : Array Nat) (divisor radix length : Nat) :
    fillPrefix points scalars divisor radix (length + 1) =
      let buckets := fillPrefix points scalars divisor radix length
      let digit := scalars[length]! / divisor % radix
      if digit != 0 then buckets.set! digit (buckets[digit]! + points[length]!) else buckets := by
  simp [fillPrefix, List.range_succ, List.foldl_append]

theorem fillPrefix_weighted (points : Array G) (scalars : Array Nat)
    (divisor radix length : Nat) (positive : 0 < radix) :
    (fillPrefix points scalars divisor radix length).size = radix ∧
      weightedBuckets (fillPrefix points scalars divisor radix length) radix =
        ∑ index ∈ Finset.range length, (scalars[index]! / divisor % radix) • points[index]! := by
  induction length with
  | zero => simp [fillPrefix, weightedBuckets_replicate]
  | succ length ih =>
    rw [fillPrefix_succ]
    let digit := scalars[length]! / divisor % radix
    have bounded : digit < radix := Nat.mod_lt _ positive
    by_cases zero : digit = 0
    · simp only [show (scalars[length]! / divisor % radix) = 0 from zero, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte]
      constructor
      · exact ih.1
      · rw [Finset.sum_range_succ]
        simpa only [show (scalars[length]! / divisor % radix) = 0 from zero, zero_nsmul, add_zero] using ih.2
    · have different : (digit != 0) = true := by simp [zero]
      simp only [show (scalars[length]! / divisor % radix) = digit from rfl, different, ↓reduceIte]
      constructor
      · simpa using ih.1
      · rw [bucket_update_weighted _ radix digit _ ih.1 bounded, ih.2, Finset.sum_range_succ]

/-- The actual fill loop's complete weighted bucket sum, not a naive MSM
replacement. Defaults and all source indexing are retained verbatim. -/
theorem fillBuckets_weighted (points : Array G) (scalars : Array Nat)
    (divisor radix : Nat) (positive : 0 < radix) :
    weightedBuckets (fillBuckets points scalars 0 (· + ·) divisor radix) radix =
      ∑ index ∈ Finset.range points.size, (scalars[index]! / divisor % radix) • points[index]! := by
  have source : fillBuckets points scalars 0 (· + ·) divisor radix =
      fillPrefix points scalars divisor radix points.size := by
    simp [fillBuckets, fillPrefix, List.range_eq_range']
    have move (condition : Prop) [Decidable condition] (yes no : Array G) :
        (if condition then (pure (ForInStep.yield yes) : Id (ForInStep (Array G)))
          else pure (ForInStep.yield no)) =
        pure (ForInStep.yield (if condition then yes else no)) := by split <;> rfl
    simp_rw [move]
    simp
  rw [source]
  exact (fillPrefix_weighted points scalars divisor radix points.size positive).2

end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.weightedBuckets_replicate
#print axioms LeanCrypto.Proofs.WindowedMSM.bucket_update_weighted
#print axioms LeanCrypto.Proofs.WindowedMSM.fillPrefix_succ
#print axioms LeanCrypto.Proofs.WindowedMSM.fillPrefix_weighted
#print axioms LeanCrypto.Proofs.WindowedMSM.fillBuckets_weighted
