import LeanCryptoProofs.WindowedMSM.GroupWindowed

set_option autoImplicit false

namespace LeanCrypto.Proofs.WindowedMSM

variable {A B : Type} [Inhabited A] [Inhabited B]

theorem map_getBang (f : A → B) (defaults : f default = default) (values : Array A) (index : Nat) :
    (values.map f)[index]! = f values[index]! := by
  simp only [getElem!_def, Array.getElem?_map]
  cases entry : values[index]? <;> simp [defaults]

theorem fillBuckets_fold (points : Array A) (scalars : Array Nat)
    (zero : A) (add : A → A → A) (divisor radix : Nat) :
    fillBuckets points scalars zero add divisor radix =
      (List.range points.size).foldl (fun buckets index =>
        let digit := scalars[index]! / divisor % radix
        if digit != 0 then buckets.set! digit (add buckets[digit]! points[index]!) else buckets)
        (Array.replicate radix zero) := by
  simp [fillBuckets, List.range_eq_range']
  have move (condition : Prop) [Decidable condition] (yes no : Array A) :
      (if condition then (pure (ForInStep.yield yes) : Id (ForInStep (Array A)))
        else pure (ForInStep.yield no)) =
      pure (ForInStep.yield (if condition then yes else no)) := by split <;> rfl
  simp_rw [move]
  simp

theorem fillBuckets_map (f : A → B) (defaults : f default = default)
    (addA : A → A → A) (addB : B → B → B)
    (adds : ∀ x y, f (addA x y) = addB (f x) (f y))
    (points : Array A) (scalars : Array Nat) (zero : A) (divisor radix : Nat) :
    (fillBuckets points scalars zero addA divisor radix).map f =
      fillBuckets (points.map f) scalars (f zero) addB divisor radix := by
  rw [fillBuckets_fold, fillBuckets_fold]
  simp only [Array.size_map]
  rw [← Array.map_replicate]
  symm
  apply List.foldl_hom (Array.map f)
  intro buckets index
  by_cases zeroDigit : scalars[index]! / divisor % radix = 0
  · simp [zeroDigit]
  · simp [zeroDigit, map_getBang f defaults, adds]

theorem collapseBuckets_map (f : A → B) (defaults : f default = default)
    (addA : A → A → A) (addB : B → B → B)
    (adds : ∀ x y, f (addA x y) = addB (f x) (f y))
    (buckets : Array A) (zero result : A) (radix : Nat) :
    f (collapseBuckets buckets zero result addA radix) =
      collapseBuckets (buckets.map f) (f zero) (f result) addB radix := by
  simp [collapseBuckets]
  have transferred := List.foldl_hom
    (fun state : MProd A A => (⟨f state.fst, f state.snd⟩ : MProd B B))
    (l := List.range' 1 (radix - 1)) (init := ⟨result, zero⟩)
    (g₁ := fun state digit =>
      let running := addA state.snd buckets[radix - digit]!
      ⟨addA state.fst running, running⟩)
    (g₂ := fun state digit =>
      let running := addB state.snd (buckets.map f)[radix - digit]!
      ⟨addB state.fst running, running⟩)
    (by intro state digit; simp [map_getBang f defaults, adds])
  exact (congrArg MProd.fst transferred).symm

theorem nativeWindowed_map (f : A → B) (defaults : f default = default)
    (addA : A → A → A) (addB : B → B → B) (doubleA : A → A) (doubleB : B → B)
    (adds : ∀ x y, f (addA x y) = addB (f x) (f y))
    (doubles : ∀ x, f (doubleA x) = doubleB (f x))
    (points : Array A) (scalars : Array Nat) (zero : A) :
    f (nativeWindowed points scalars zero addA doubleA) =
      nativeWindowed (points.map f) scalars (f zero) addB doubleB := by
  rw [nativeWindowed_eq_components, nativeWindowed_eq_components]
  simp [windowedComponents]
  simp only [← List.range_eq_range']
  symm
  apply List.foldl_hom f
  intro result window
  have doubling := List.foldl_hom f
    (l := List.range (bits points.size)) (init := result)
    (g₁ := fun state _ => doubleA state) (g₂ := fun state _ => doubleB state)
    (by intro state _; exact (doubles state).symm)
  rw [doubling, ← fillBuckets_map f defaults addA addB adds,
    ← collapseBuckets_map f defaults addA addB adds]

end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.map_getBang
#print axioms LeanCrypto.Proofs.WindowedMSM.fillBuckets_fold
#print axioms LeanCrypto.Proofs.WindowedMSM.fillBuckets_map
#print axioms LeanCrypto.Proofs.WindowedMSM.collapseBuckets_map
#print axioms LeanCrypto.Proofs.WindowedMSM.nativeWindowed_map
