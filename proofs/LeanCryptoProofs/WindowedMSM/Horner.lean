import LeanCryptoProofs.WindowedMSM.BucketFill
import LeanCryptoProofs.WindowedMSM.BucketCollapse

set_option autoImplicit false

namespace LeanCrypto.Proofs.WindowedMSM

variable {G : Type} [AddCommMonoid G]

theorem bucket_stage [Inhabited G] (points : Array G) (scalars : Array Nat)
    (divisor radix : Nat) (positive : 0 < radix) (result : G) :
    collapseBuckets (fillBuckets points scalars 0 (· + ·) divisor radix) 0 result (· + ·) radix =
      result + ∑ index ∈ Finset.range points.size, (scalars[index]! / divisor % radix) • points[index]! := by
  rw [collapseBuckets_weighted]
  change result + weightedBuckets (fillBuckets points scalars 0 (· + ·) divisor radix) radix = _
  rw [fillBuckets_weighted points scalars divisor radix positive]

theorem double_fold (length : Nat) (result : G) :
    (List.range length).foldl (fun accumulator _ => accumulator + accumulator) result =
      (2 ^ length) • result := by
  induction length with
  | zero => simp
  | succ length ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih, ← add_nsmul, pow_succ, Nat.mul_two]

def reverseHorner (radix length : Nat) (coefficient : Nat → G) (initial : G) : G :=
  (List.range length).foldl (fun result window => radix • result + coefficient (length - 1 - window)) initial

theorem reverseHorner_succ (radix length : Nat) (coefficient : Nat → G) (initial : G) :
    reverseHorner radix (length + 1) coefficient initial =
      reverseHorner radix length coefficient (radix • initial + coefficient length) := by
  unfold reverseHorner
  rw [List.range_succ_eq_map]
  simp only [List.foldl_cons, List.foldl_map, Nat.add_sub_cancel, Nat.sub_zero]
  have equal : (fun n : Nat => coefficient (length - (n + 1))) =
      (fun n : Nat => coefficient (length - 1 - n)) := by
    funext n
    congr 1
    omega
  exact congrArg (fun f : Nat → G =>
    (List.range length).foldl (fun result window => radix • result + f window)
      (radix • initial + coefficient length)) equal

theorem reverseHorner_sum (radix length : Nat) (coefficient : Nat → G) (initial : G) :
    reverseHorner radix length coefficient initial =
      radix ^ length • initial + ∑ index ∈ Finset.range length, radix ^ index • coefficient index := by
  induction length generalizing initial with
  | zero => simp [reverseHorner]
  | succ length ih =>
    rw [reverseHorner_succ, ih, nsmul_add, ← mul_nsmul, ← pow_succ', Finset.sum_range_succ]
    simp only [add_assoc, add_left_comm, add_comm]

theorem native_group_horner [Inhabited G] (points : Array G) (scalars : Array Nat) :
    nativeWindowed points scalars 0 (· + ·) (fun point => point + point) =
      reverseHorner (radix points.size) (windows points.size)
        (fun index => ∑ i ∈ Finset.range points.size,
          (scalars[i]! / 2 ^ (index * bits points.size) % radix points.size) • points[i]!) 0 := by
  rw [nativeWindowed_eq_components]
  simp [windowedComponents]
  have positive : 0 < radix points.size := pow_pos (by decide) _
  simp_rw [bucket_stage points scalars _ _ positive]
  simp only [← List.range_eq_range', double_fold]
  rfl

end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.bucket_stage
#print axioms LeanCrypto.Proofs.WindowedMSM.double_fold
#print axioms LeanCrypto.Proofs.WindowedMSM.reverseHorner_succ
#print axioms LeanCrypto.Proofs.WindowedMSM.reverseHorner_sum
#print axioms LeanCrypto.Proofs.WindowedMSM.native_group_horner
