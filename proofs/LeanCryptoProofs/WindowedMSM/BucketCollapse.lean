import LeanCryptoProofs.WindowedMSM.WindowedSource
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace LeanCrypto.Proofs.WindowedMSM

variable {G : Type} [AddCommMonoid G]

def collapseRun (values : List G) (running result : G) : G × G :=
  values.foldl (fun state value =>
    let next := state.1 + value
    (next, state.2 + next)) (running, result)

def weightedList : List G → G
  | [] => 0
  | value :: tail => (tail.length + 1) • value + weightedList tail

theorem collapseRun_snd (values : List G) (running result : G) :
    (collapseRun values running result).2 =
      result + values.length • running + weightedList values := by
  induction values generalizing running result with
  | nil => simp [collapseRun, weightedList]
  | cons value tail ih =>
    change (collapseRun tail (running + value) (result + (running + value))).2 = _
    rw [ih]
    simp only [List.length_cons, weightedList, nsmul_add, add_nsmul, one_nsmul]
    simp only [add_assoc, add_left_comm, add_comm]

theorem weightedList_range (f : Nat → G) (start length : Nat) :
    weightedList ((List.range' start length).map f) =
      ∑ index ∈ Finset.range length, (length - index) • f (start + index) := by
  induction length generalizing start with
  | zero => simp [weightedList]
  | succ length ih =>
    simp [List.range'_succ, weightedList, ih, Finset.sum_range_succ',
      Nat.add_left_comm, add_comm]

theorem collapseBuckets_eq_run [Inhabited G] (buckets : Array G) (result : G) (radix : Nat) :
    collapseBuckets buckets 0 result (· + ·) radix =
      (collapseRun ((List.range' 1 (radix - 1)).map (fun digit => buckets[radix - digit]!)) 0 result).2 := by
  simp [collapseBuckets, collapseRun, List.foldl_map]
  have transferred := List.foldl_hom (fun state : MProd G G => (state.snd, state.fst))
    (l := List.range' 1 (radix - 1)) (init := ⟨result, 0⟩)
    (g₁ := fun state digit =>
      let running := state.snd + buckets[radix - digit]!
      ⟨state.fst + running, running⟩)
    (g₂ := fun state digit =>
      let running := state.1 + buckets[radix - digit]!
      (running, state.2 + running)) (by intros; rfl)
  exact (congrArg Prod.snd transferred).symm

/-- The exact descending running-sum stage in the actual native source
assigns each bucket precisely its radix digit multiplicity. -/
theorem collapseBuckets_weighted [Inhabited G] (buckets : Array G) (result : G) (radix : Nat) :
    collapseBuckets buckets 0 result (· + ·) radix =
      result + ∑ digit ∈ Finset.range radix, digit • buckets[digit]! := by
  rw [collapseBuckets_eq_run, collapseRun_snd]
  simp only [nsmul_zero, add_zero]
  rw [weightedList_range]
  cases radix with
  | zero => simp
  | succ n =>
    have reflection := Finset.sum_range_reflect (fun digit => digit • buckets[digit]!) (n + 1)
    conv at reflection =>
      lhs
      rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, zero_nsmul, add_zero] at reflection
    apply congrArg (fun value => result + value)
    have index : ∀ i : Nat, n + 1 - (1 + i) = n - i := by intro i; omega
    simpa only [Nat.add_sub_cancel, index] using reflection

end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.collapseRun_snd
#print axioms LeanCrypto.Proofs.WindowedMSM.weightedList_range
#print axioms LeanCrypto.Proofs.WindowedMSM.collapseBuckets_eq_run
#print axioms LeanCrypto.Proofs.WindowedMSM.collapseBuckets_weighted
