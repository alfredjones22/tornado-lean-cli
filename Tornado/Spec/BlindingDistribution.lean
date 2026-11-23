import Tornado.Runtime.ProofBlinding

/-!
Exact finite counting for the sampler's shared lazy `sampleLoop`.
An ideal draw has D equally likely decoded values 0..D-1, independently of
all other draws and the witness. For production D=2^256. This is an explicit
contract for the OS entropy/byte-decoding boundary, not a theorem about the
kernel CSPRNG. Counts pad unread independent coordinates, so early return
and sequential sampling do not assume disjoint fixed-size read blocks.
Malformed reads and IO errors are outside that ideal well-formed contract.
-/

namespace Tornado.Spec.BlindingDistribution

open Tornado.Runtime.ProofBlinding

def sumTo : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

theorem sumTo_congr (n : Nat) (f g : Nat → Nat)
    (h : ∀ i, i < n → f i = g i) : sumTo n f = sumTo n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumTo]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sumTo_add (n : Nat) (f g : Nat → Nat) :
    sumTo n (fun x => f x + g x) = sumTo n f + sumTo n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumTo, ih]; omega

theorem sumTo_scale (n c : Nat) (f : Nat → Nat) :
    sumTo n (fun x => c * f x) = c * sumTo n f := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp [sumTo, ih, Nat.mul_add]

theorem sumTo_const (n c : Nat) : sumTo n (fun _ => c) = n * c := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp [sumTo, ih, Nat.add_mul]

theorem sumTo_split (n k : Nat) (f : Nat → Nat) :
    sumTo (n + k) f = sumTo n f + sumTo k (fun i => f (n + i)) := by
  induction k with
  | zero => simp [sumTo]
  | succ k ih => simp [sumTo, ih, Nat.add_assoc]

theorem sumTo_delta (n value : Nat) :
    sumTo n (fun x => if x = value then 1 else 0) = if value < n then 1 else 0 := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    by_cases equal : n = value
    · subst value; simp [sumTo, ih]
    · by_cases inside : value < n
      · simp [sumTo, ih, equal, inside, Nat.lt_succ_of_lt inside]
      · have outside : ¬ value < n + 1 := by omega
        simp [sumTo, ih, equal, inside, outside]

/-- Partition the actual draw alphabet by its exact runtime decision.
There is one accepted draw per allowed scalar and D-(q-1) retry draws. -/
theorem sumTo_admissible (D q c : Nat) (f : Nat → Nat)
    (positive : 0 < q) (fits : q ≤ D) :
    sumTo D (fun x => if admissible q x then f x else c) =
      sumTo (q - 1) (fun i => f (i + 1)) + (D - (q - 1)) * c := by
  have splitD : D = 1 + (q - 1) + (D - q) := by omega
  rw [show sumTo D (fun x => if admissible q x then f x else c) =
      sumTo (1 + (q - 1) + (D - q)) (fun x => if admissible q x then f x else c)
    from congrArg (fun n => sumTo n (fun x => if admissible q x then f x else c)) splitD]
  rw [sumTo_split, sumTo_split]
  have first : sumTo 1 (fun x => if admissible q x then f x else c) = c := by
    simp [sumTo, admissible]
  rw [first]
  have accepted : sumTo (q - 1) (fun i =>
      if admissible q (1 + i) then f (1 + i) else c) =
      sumTo (q - 1) (fun i => f (i + 1)) := by
    apply sumTo_congr
    intro i hi
    have h : admissible q (1 + i) = true := by simp only [admissible, decide_eq_true_eq]; omega
    rw [h]
    simp [Nat.add_comm]
  rw [accepted]
  have rejected : sumTo (D - q) (fun i =>
      if admissible q (1 + (q - 1) + i) then f (1 + (q - 1) + i) else c) =
      (D - q) * c := by
    rw [← sumTo_const]
    apply sumTo_congr
    intro i _
    have h : ¬ (0 < 1 + (q - 1) + i ∧ 1 + (q - 1) + i < q) := by omega
    simp [admissible, h]
  rw [rejected]
  have retries : D - (q - 1) = (D - q) + 1 := by omega
  rw [retries, Nat.add_mul]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A mathematical observation tree. This is an interpretation of the shared
monadic sampler, not a second independently written retry loop. -/
inductive DrawTree (α : Type) where
  | done : α → DrawTree α
  | abort : DrawTree α
  | draw : (Nat → DrawTree α) → DrawTree α

namespace DrawTree

def bind (tree : DrawTree α) (next : α → DrawTree β) : DrawTree β :=
  match tree with
  | .done value => next value
  | .abort => .abort
  | .draw branch => .draw (fun value => bind (branch value) next)

instance : Monad DrawTree where
  pure := DrawTree.done
  bind := DrawTree.bind

/-- Number of length-budget ideal draw streams producing an observation.
Unused coordinates are counted, never read by the runtime program. -/
def count (D : Nat) : Nat → DrawTree α → (Option α → Nat) → Nat
  | n, .done value, event => D ^ n * event (some value)
  | n, .abort, event => D ^ n * event none
  | 0, .draw _, _ => 0
  | n + 1, .draw branch, event => sumTo D (fun x => count D n (branch x) event)

def Bounded : Nat → DrawTree α → Prop
  | _, .done _ => True
  | _, .abort => True
  | 0, .draw _ => False
  | n + 1, .draw branch => ∀ x, Bounded n (branch x)

theorem count_congr (D n : Nat) (tree : DrawTree α) (f g : Option α → Nat)
    (h : ∀ result, f result = g result) : count D n tree f = count D n tree g := by
  have equal : f = g := funext h
  rw [equal]

theorem count_scale (D n c : Nat) (tree : DrawTree α) (event : Option α → Nat) :
    count D n tree (fun x => c * event x) = c * count D n tree event := by
  induction n generalizing tree with
  | zero => cases tree <;> simp [count, Nat.mul_left_comm]
  | succ n ih =>
    cases tree with
    | done _ => simp [count, Nat.mul_left_comm]
    | abort => simp [count, Nat.mul_left_comm]
    | draw branch => simp only [count]; rw [← sumTo_scale]; apply sumTo_congr; intro x _; apply ih

theorem count_add (D n : Nat) (tree : DrawTree α) (f g : Option α → Nat) :
    count D n tree (fun x => f x + g x) = count D n tree f + count D n tree g := by
  induction n generalizing tree with
  | zero => cases tree <;> simp [count, Nat.mul_add]
  | succ n ih =>
    cases tree with
    | done _ => simp [count, Nat.mul_add]
    | abort => simp [count, Nat.mul_add]
    | draw branch => simp only [count]; rw [← sumTo_add]; apply sumTo_congr; intro x _; apply ih

theorem count_total (D n : Nat) (tree : DrawTree α) (bounded : Bounded n tree) :
    count D n tree (fun _ => 1) = D ^ n := by
  induction n generalizing tree with
  | zero => cases tree <;> simp_all [count, Bounded]
  | succ n ih =>
    cases tree with
    | done _ => simp [count]
    | abort => simp [count]
    | draw branch =>
      simp only [count]
      calc
        sumTo D (fun x => count D n (branch x) (fun _ => 1)) = sumTo D (fun _ => D ^ n) :=
          sumTo_congr _ _ _ (fun x _ => ih _ (bounded x))
        _ = D ^ (n + 1) := by rw [sumTo_const, Nat.pow_succ]; exact Nat.mul_comm _ _

theorem count_padding (D n extra : Nat) (tree : DrawTree α)
    (bounded : Bounded n tree) (event : Option α → Nat) :
    count D (n + extra) tree event = D ^ extra * count D n tree event := by
  induction n generalizing tree with
  | zero => cases tree <;> simp_all [count, Bounded]
  | succ n ih =>
    cases tree with
    | done _ => simp [count, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    | abort => simp [count, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    | draw branch =>
      rw [show n + 1 + extra = (n + extra) + 1 by omega]
      simp only [count]
      rw [← sumTo_scale]
      apply sumTo_congr
      intro x _
      exact ih _ (bounded x)

theorem bounded_mono (n extra : Nat) (tree : DrawTree α) (bounded : Bounded n tree) :
    Bounded (n + extra) tree := by
  induction n generalizing tree with
  | zero => cases tree <;> simp_all [Bounded]
  | succ n ih =>
    cases tree with
    | done _ => simp [Bounded]
    | abort => simp [Bounded]
    | draw branch =>
      rw [show n + 1 + extra = (n + extra) + 1 by omega]
      intro x
      exact ih _ (bounded x)

theorem bounded_bind (n m : Nat) (tree : DrawTree α) (next : α → DrawTree β)
    (bounded : Bounded n tree) (tail : ∀ value, Bounded m (next value)) :
    Bounded (n + m) (tree.bind next) := by
  induction n generalizing tree with
  | zero =>
    cases tree with
    | done value => simpa [bind] using tail value
    | abort => simp [bind, Bounded]
    | draw _ => exact False.elim bounded
  | succ n ih =>
    cases tree with
    | done value =>
      simpa [bind, Nat.add_comm] using bounded_mono m (n + 1) (next value) (tail value)
    | abort => simp [bind, Bounded]
    | draw branch =>
      rw [show n + 1 + m = (n + m) + 1 by omega]
      intro x
      exact ih _ (bounded x)

/-- Sequential continuations start at the next unread coordinate. This exact
count identity establishes the stopping-time bridge needed by pair sampling. -/
theorem count_bind (D n m : Nat) (tree : DrawTree α) (next : α → DrawTree β)
    (bounded : Bounded n tree) (tail : ∀ value, Bounded m (next value))
    (event : Option β → Nat) :
    count D (n + m) (tree.bind next) event =
      count D n tree (fun result => match result with
        | none => D ^ m * event none
        | some value => count D m (next value) event) := by
  induction n generalizing tree with
  | zero => cases tree <;> simp_all [bind, count, Bounded]
  | succ n ih =>
    cases tree with
    | done value =>
      simpa [bind, count, Nat.add_comm] using
        count_padding D m (n + 1) (next value) (tail value) event
    | abort => simp [bind, count, Nat.pow_add, Nat.mul_assoc]
    | draw branch =>
      rw [show n + 1 + m = (n + m) + 1 by omega]
      simp only [bind, count]
      apply sumTo_congr
      intro x _
      exact ih _ (bounded x)

end DrawTree

def candidate (q value : Nat) : Option Nat :=
  if admissible q value then some value else none

def sampler (q budget : Nat) : DrawTree Nat :=
  sampleLoop (.draw (fun value => .done (candidate q value))) .abort budget

theorem sampler_bounded (q budget : Nat) : DrawTree.Bounded budget (sampler q budget) := by
  induction budget with
  | zero => trivial
  | succ n ih =>
    simp only [sampler, sampleLoop] at ih ⊢
    change ∀ value, DrawTree.Bounded n _
    intro value
    simp only [Pure.pure, DrawTree.bind]
    cases candidate q value with
    | some accepted => simp [DrawTree.Bounded]
    | none => exact ih

def mass (D q budget : Nat) (event : Option Nat → Nat) : Nat :=
  DrawTree.count D budget (sampler q budget) event

/-- Derived from the shared loop's first draw and its exact admissible-value
partition, rather than postulating uniform output weights. -/
theorem mass_succ (D q budget : Nat) (event : Option Nat → Nat)
    (positive : 0 < q) (fits : q ≤ D) :
    mass D q (budget + 1) event =
      D ^ budget * sumTo (q - 1) (fun i => event (some (i + 1))) +
      (D - (q - 1)) * mass D q budget event := by
  simp only [mass, sampler, sampleLoop, Bind.bind, Pure.pure, DrawTree.bind, DrawTree.count]
  calc
    _ = sumTo D (fun value => if admissible q value then D ^ budget * event (some value)
        else DrawTree.count D budget
          (sampleLoop (.draw (fun v => .done (candidate q v))) .abort budget) event) := by
      apply sumTo_congr
      intro value _
      by_cases allowed : admissible q value = true
      · simp [candidate, allowed, DrawTree.count]
      · simp [candidate, allowed]
    _ = _ := by rw [sumTo_admissible D q _ _ positive fits, sumTo_scale]

/-- The model's decoded-value decision is exactly the runtime decision after
erasing Scalar's proof fields. This does not assume a second classifier. -/
theorem runtime_candidate_matches (value : Nat) :
    (admitValue value).map (fun scalar => scalar.value) =
      candidate Tornado.Protocol.Groth16R1CS.scalarPrime value := by
  unfold admitValue candidate
  split <;> simp_all

def retryCount (D q : Nat) : Nat := D - (q - 1)

def successWeight (D q : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => D ^ n + retryCount D q * successWeight D q n

def valueEvent (value : Nat) : Option Nat → Nat
  | some actual => if actual = value then 1 else 0
  | none => 0

def successEvent : Option α → Nat
  | some _ => 1
  | none => 0

def failureEvent : Option α → Nat
  | some _ => 0
  | none => 1

theorem accepted_delta (q value : Nat) (positive : 0 < q) :
    sumTo (q - 1) (fun i => valueEvent value (some (i + 1))) =
      if admissible q value then 1 else 0 := by
  by_cases allowed : admissible q value = true
  · have bounds : 0 < value ∧ value < q := of_decide_eq_true allowed
    have eq : ∀ i, (if i + 1 = value then 1 else 0) =
        (if i = value - 1 then 1 else 0) := by
      intro i
      have equivalent : i + 1 = value ↔ i = value - 1 := by omega
      simp only [equivalent]
    simp only [valueEvent]
    rw [sumTo_congr _ _ _ (fun i _ => eq i), sumTo_delta]
    simp [allowed, show value - 1 < q - 1 by omega]
  · have invalid : ¬ (0 < value ∧ value < q) := by
      simpa [admissible] using allowed
    rw [show (if admissible q value then 1 else 0) = 0 by simp [allowed]]
    calc
      sumTo (q - 1) (fun i => valueEvent value (some (i + 1))) = sumTo (q - 1) (fun _ => 0) := by
        apply sumTo_congr
        intro i hi
        have different : i + 1 ≠ value := by omega
        simp [valueEvent, different]
      _ = 0 := by simp [sumTo_const]

theorem scalar_count (D q budget value : Nat) (positive : 0 < q) (fits : q ≤ D) :
    mass D q budget (valueEvent value) =
      if admissible q value then successWeight D q budget else 0 := by
  induction budget with
  | zero => simp [mass, sampler, sampleLoop, DrawTree.count, valueEvent, successWeight]
  | succ n ih =>
    rw [mass_succ D q n _ positive fits, accepted_delta q value positive, ih]
    by_cases allowed : admissible q value = true
    · simp [allowed, successWeight, retryCount]
    · simp [allowed]

theorem exhaustion_count (D q budget : Nat) (positive : 0 < q) (fits : q ≤ D) :
    mass D q budget failureEvent = retryCount D q ^ budget := by
  induction budget with
  | zero => simp [mass, sampler, sampleLoop, DrawTree.count, failureEvent]
  | succ n ih =>
    rw [mass_succ D q n _ positive fits]
    simp [failureEvent, sumTo_const, ih, Nat.pow_succ, retryCount, Nat.mul_comm]

theorem total_count (D q budget : Nat) : mass D q budget (fun _ => 1) = D ^ budget :=
  DrawTree.count_total D budget (sampler q budget) (sampler_bounded q budget)

theorem success_count (D q budget : Nat) (positive : 0 < q) (fits : q ≤ D) :
    mass D q budget successEvent = (q - 1) * successWeight D q budget := by
  induction budget with
  | zero => simp [mass, sampler, sampleLoop, DrawTree.count, successEvent, successWeight]
  | succ n ih =>
    rw [mass_succ D q n _ positive fits]
    simp [successEvent, sumTo_const, ih, successWeight, retryCount,
      Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]

/-- All D^budget equally weighted input streams are accounted for: a returned
scalar or retry exhaustion. There is no unmodeled successful-output mass. -/
theorem normalization (D q budget : Nat) (positive : 0 < q) (fits : q ≤ D) :
    (q - 1) * successWeight D q budget + retryCount D q ^ budget = D ^ budget := by
  have split := DrawTree.count_add D budget (sampler q budget) successEvent failureEvent
  have constant : (fun result : Option Nat => successEvent result + failureEvent result) =
      (fun _ => 1) := by funext result; cases result <;> rfl
  rw [constant] at split
  change mass D q budget (fun _ => 1) =
    mass D q budget successEvent + mass D q budget failureEvent at split
  rw [total_count, success_count D q budget positive fits,
    exhaustion_count D q budget positive fits] at split
  exact split.symm

theorem successWeight_positive (D q budget : Nat) (draws : 0 < D) (budgetPositive : 0 < budget) :
    0 < successWeight D q budget := by
  cases budget with
  | zero => omega
  | succ n =>
    simp only [successWeight]
    exact Nat.lt_of_lt_of_le (Nat.pow_pos draws) (Nat.le_add_right _ _)

/-- Exact conditional uniformity in cross-multiplied integer form:
P[output=value and success] / P[success] = 1/(q-1).
For q>1 and budget>0 the denominator is positive. -/
theorem conditional_uniform (D q budget value : Nat)
    (positive : 0 < q) (fits : q ≤ D) (allowed : admissible q value = true) :
    mass D q budget (valueEvent value) * (q - 1) =
      mass D q budget successEvent := by
  rw [scalar_count D q budget value positive fits, if_pos allowed,
    success_count D q budget positive fits]
  exact Nat.mul_comm _ _

theorem success_denominator_positive (D q budget : Nat)
    (qPositive : 1 < q) (fits : q ≤ D) (budgetPositive : 0 < budget) :
    0 < mass D q budget successEvent := by
  rw [success_count D q budget (by omega) fits]
  exact Nat.mul_pos (by omega) (successWeight_positive D q budget (by omega) budgetPositive)

end Tornado.Spec.BlindingDistribution

#print axioms Tornado.Spec.BlindingDistribution.sumTo_congr
#print axioms Tornado.Spec.BlindingDistribution.sumTo_add
#print axioms Tornado.Spec.BlindingDistribution.sumTo_scale
#print axioms Tornado.Spec.BlindingDistribution.sumTo_const
#print axioms Tornado.Spec.BlindingDistribution.sumTo_split
#print axioms Tornado.Spec.BlindingDistribution.sumTo_delta
#print axioms Tornado.Spec.BlindingDistribution.sumTo_admissible
#print axioms Tornado.Spec.BlindingDistribution.DrawTree.count_congr
#print axioms Tornado.Spec.BlindingDistribution.DrawTree.count_scale
#print axioms Tornado.Spec.BlindingDistribution.DrawTree.count_add
#print axioms Tornado.Spec.BlindingDistribution.DrawTree.count_total
#print axioms Tornado.Spec.BlindingDistribution.DrawTree.count_padding
#print axioms Tornado.Spec.BlindingDistribution.DrawTree.bounded_mono
#print axioms Tornado.Spec.BlindingDistribution.DrawTree.bounded_bind
#print axioms Tornado.Spec.BlindingDistribution.DrawTree.count_bind
#print axioms Tornado.Spec.BlindingDistribution.sampler_bounded
#print axioms Tornado.Spec.BlindingDistribution.mass_succ
#print axioms Tornado.Spec.BlindingDistribution.runtime_candidate_matches
#print axioms Tornado.Spec.BlindingDistribution.accepted_delta
#print axioms Tornado.Spec.BlindingDistribution.scalar_count
#print axioms Tornado.Spec.BlindingDistribution.exhaustion_count
#print axioms Tornado.Spec.BlindingDistribution.total_count
#print axioms Tornado.Spec.BlindingDistribution.success_count
#print axioms Tornado.Spec.BlindingDistribution.normalization
#print axioms Tornado.Spec.BlindingDistribution.successWeight_positive
#print axioms Tornado.Spec.BlindingDistribution.conditional_uniform
#print axioms Tornado.Spec.BlindingDistribution.success_denominator_positive
