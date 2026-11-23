import Tornado.Spec.BlindingDistribution

/-! Sequential pair distribution for the actual shared samplePairLoop.
The next sampler starts at the next unread independent entropy coordinate.
Success, retry exhaustion and ignored trailing coordinates are all counted.
-/

namespace Tornado.Spec.BlindingDistribution

open Tornado.Runtime.ProofBlinding

theorem DrawTree.count_zero (D n : Nat) (tree : DrawTree α) :
    DrawTree.count D n tree (fun _ => 0) = 0 := by
  simpa using DrawTree.count_scale D n 0 tree (fun _ => 1)

theorem DrawTree.count_map (D n : Nat) (tree : DrawTree α) (f : α → β)
    (bounded : DrawTree.Bounded n tree) (event : Option β → Nat) :
    DrawTree.count D n (tree.bind (fun value => .done (f value))) event =
      DrawTree.count D n tree (fun result => match result with
        | none => event none
        | some value => event (some (f value))) := by
  have equation := DrawTree.count_bind D n 0 tree
    (fun value => .done (f value)) bounded (fun _ => trivial) event
  simpa [DrawTree.count] using equation

def pairSampler (q budget : Nat) : DrawTree (Nat × Nat) :=
  samplePairLoop (.draw (fun value => .done (candidate q value))) .abort budget

theorem pairSampler_equation (q budget : Nat) :
    pairSampler q budget = (sampler q budget).bind (fun r =>
      (sampler q budget).bind (fun s => .done (r, s))) := by
  rfl

theorem pairSampler_bounded (q budget : Nat) :
    DrawTree.Bounded (budget + budget) (pairSampler q budget) := by
  rw [pairSampler_equation]
  apply DrawTree.bounded_bind
  · exact sampler_bounded q budget
  · intro r
    have bounded := DrawTree.bounded_bind budget 0 (sampler q budget)
      (fun s => .done (r, s)) (sampler_bounded q budget) (fun _ => trivial)
    simpa using bounded

def pairMass (D q budget : Nat) (event : Option (Nat × Nat) → Nat) : Nat :=
  DrawTree.count D (budget + budget) (pairSampler q budget) event

def pairValueEvent (r s : Nat) : Option (Nat × Nat) → Nat
  | some (a, b) => if a = r ∧ b = s then 1 else 0
  | none => 0

theorem pair_continuation (D q budget r wantedR wantedS : Nat) :
    DrawTree.count D budget ((sampler q budget).bind (fun s => .done (r, s)))
      (pairValueEvent wantedR wantedS) =
      if r = wantedR then mass D q budget (valueEvent wantedS) else 0 := by
  rw [DrawTree.count_map D budget _ _ (sampler_bounded q budget)]
  by_cases equal : r = wantedR
  · subst r
    rw [if_pos rfl]
    unfold mass
    apply DrawTree.count_congr
    intro result
    cases result <;> simp [pairValueEvent, valueEvent]
  · rw [if_neg equal, ← DrawTree.count_zero D budget (sampler q budget)]
    apply DrawTree.count_congr
    intro result
    cases result <;> simp [pairValueEvent, equal]

/-- Exact product count derived from sequential execution. It does not assume
that the two samplers consume fixed or disjoint preallocated read blocks. -/
theorem pair_joint_factorizes (D q budget r s : Nat) :
    pairMass D q budget (pairValueEvent r s) =
      mass D q budget (valueEvent r) * mass D q budget (valueEvent s) := by
  unfold pairMass
  rw [pairSampler_equation]
  have tail : ∀ r : Nat, DrawTree.Bounded budget
      ((sampler q budget).bind (fun s => .done (r, s))) := by
    intro r
    simpa using DrawTree.bounded_bind budget 0 (sampler q budget)
      (fun s => .done (r, s)) (sampler_bounded q budget) (fun _ => trivial)
  rw [DrawTree.count_bind D budget budget _ _ (sampler_bounded q budget) tail]
  calc
    _ = DrawTree.count D budget (sampler q budget)
        (fun result => mass D q budget (valueEvent s) * valueEvent r result) := by
      apply DrawTree.count_congr
      intro result
      cases result with
      | none => simp [pairValueEvent, valueEvent]
      | some value =>
        simp only []
        rw [pair_continuation]
        by_cases same : value = r <;> simp [valueEvent, same]
    _ = _ := by rw [DrawTree.count_scale]; exact Nat.mul_comm _ _

theorem pair_success_count (D q budget : Nat) :
    pairMass D q budget successEvent = mass D q budget successEvent ^ 2 := by
  unfold pairMass
  rw [pairSampler_equation]
  have tail : ∀ r : Nat, DrawTree.Bounded budget
      ((sampler q budget).bind (fun s => .done (r, s))) := by
    intro r
    simpa using DrawTree.bounded_bind budget 0 (sampler q budget)
      (fun s => .done (r, s)) (sampler_bounded q budget) (fun _ => trivial)
  rw [DrawTree.count_bind D budget budget _ _ (sampler_bounded q budget) tail]
  calc
    _ = DrawTree.count D budget (sampler q budget)
        (fun result => mass D q budget successEvent * successEvent result) := by
      apply DrawTree.count_congr
      intro result
      cases result with
      | none => simp [successEvent]
      | some value =>
        simp only []
        rw [DrawTree.count_map D budget _ _ (sampler_bounded q budget)]
        simp only [successEvent, Nat.mul_one]
        apply DrawTree.count_congr
        intro input
        cases input <;> rfl
    _ = _ := by rw [DrawTree.count_scale]; simp [mass, Nat.pow_succ]

theorem pair_normalization (D q budget : Nat) :
    pairMass D q budget successEvent + pairMass D q budget failureEvent = D ^ (budget + budget) := by
  have split := DrawTree.count_add D (budget + budget) (pairSampler q budget)
    successEvent failureEvent
  have constant : (fun result : Option (Nat × Nat) => successEvent result + failureEvent result) =
      (fun _ => 1) := by funext result; cases result <;> rfl
  rw [constant, DrawTree.count_total D (budget + budget) _ (pairSampler_bounded q budget)] at split
  exact split.symm

/-- Equality of conditional probabilities expressed without division:
P[r=a,s=b | both succeed] = P[r=a | succeeds] P[s=b | succeeds].
Denominators are positive for D>=q>1 and a positive draw budget. -/
theorem conditional_pair_independent (D q budget r s : Nat) :
    pairMass D q budget (pairValueEvent r s) * mass D q budget successEvent ^ 2 =
      (mass D q budget (valueEvent r) * mass D q budget (valueEvent s)) *
        pairMass D q budget successEvent := by
  rw [pair_joint_factorizes, pair_success_count]

theorem conditional_pair_uniform (D q budget r s : Nat)
    (positive : 0 < q) (fits : q ≤ D)
    (allowedR : admissible q r = true) (allowedS : admissible q s = true) :
    pairMass D q budget (pairValueEvent r s) * (q - 1) ^ 2 =
      pairMass D q budget successEvent := by
  rw [pair_joint_factorizes, pair_success_count,
    scalar_count D q budget r positive fits, scalar_count D q budget s positive fits,
    if_pos allowedR, if_pos allowedS, success_count D q budget positive fits]
  simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem pair_success_denominator_positive (D q budget : Nat)
    (qPositive : 1 < q) (fits : q ≤ D) (budgetPositive : 0 < budget) :
    0 < pairMass D q budget successEvent := by
  rw [pair_success_count]
  exact Nat.pow_pos (success_denominator_positive D q budget qPositive fits budgetPositive)

end Tornado.Spec.BlindingDistribution

#print axioms Tornado.Spec.BlindingDistribution.DrawTree.count_zero
#print axioms Tornado.Spec.BlindingDistribution.DrawTree.count_map
#print axioms Tornado.Spec.BlindingDistribution.pairSampler_equation
#print axioms Tornado.Spec.BlindingDistribution.pairSampler_bounded
#print axioms Tornado.Spec.BlindingDistribution.pair_continuation
#print axioms Tornado.Spec.BlindingDistribution.pair_joint_factorizes
#print axioms Tornado.Spec.BlindingDistribution.pair_success_count
#print axioms Tornado.Spec.BlindingDistribution.pair_normalization
#print axioms Tornado.Spec.BlindingDistribution.conditional_pair_independent
#print axioms Tornado.Spec.BlindingDistribution.conditional_pair_uniform
#print axioms Tornado.Spec.BlindingDistribution.pair_success_denominator_positive
