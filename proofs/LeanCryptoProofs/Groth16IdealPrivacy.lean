import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Ideal algebraic mask transport only. No theorem below connects field offsets
to the application's coordinates, MSM, pairing, QAP, proving key, encoding,
release process, OS entropy, timings, erasure, or history/RPC observations.
An observation may depend only on the ideal triple and fixed public setup.
-/

namespace IdealGroth16

attribute [local instance] Classical.propDecidable

structure Setup (F : Type*) [Field F] where
  alpha : F
  beta : F
  gamma : F
  publicIC : F
  delta : F
  delta_ne_zero : delta ≠ 0

def Setup.kappa {F : Type*} [Field F] (p : Setup F) : F :=
  p.alpha * p.beta + p.gamma * p.publicIC

structure WitnessOffsets {F : Type*} [Field F] (p : Setup F) where
  A : F
  B : F
  K : F
  compatible : p.delta * K = A * B - p.kappa

structure Triple (F : Type*) where
  a : F
  b : F
  c : F

theorem Triple.ext {F : Type*} {x y : Triple F}
    (a : x.a = y.a) (b : x.b = y.b) (c : x.c = y.c) : x = y := by
  cases x
  cases y
  simp_all

/-- The requested Groth16 scalar formula, before any group-coordinate or
encoding implementation is attached. -/
def output {F : Type*} [Field F] {p : Setup F} (w : WitnessOffsets p) (m : F × F) : Triple F :=
  let a := w.A + m.1 * p.delta
  let b := w.B + m.2 * p.delta
  ⟨a, b, w.K + m.2 * a + m.1 * b - m.1 * m.2 * p.delta⟩

theorem output_canonical_c {F : Type*} [Field F] {p : Setup F}
    (w : WitnessOffsets p) (m : F × F) :
    (output w m).c = ((output w m).a * (output w m).b - p.kappa) / p.delta := by
  apply (eq_div_iff p.delta_ne_zero).2
  change (w.K + m.2 * (w.A + m.1 * p.delta) + m.1 * (w.B + m.2 * p.delta) -
    m.1 * m.2 * p.delta) * p.delta =
    (w.A + m.1 * p.delta) * (w.B + m.2 * p.delta) - p.kappa
  calc
    _ = p.delta * w.K +
        ((w.A + m.1 * p.delta) * (w.B + m.2 * p.delta) - w.A * w.B) := by ring
    _ = _ := by rw [w.compatible]; ring

def canonicalTriple {F : Type*} [Field F] (p : Setup F) (a b : F) : Triple F :=
  ⟨a, b, (a * b - p.kappa) / p.delta⟩

theorem output_eq_canonical {F : Type*} [Field F] {p : Setup F}
    (w : WitnessOffsets p) (m : F × F) :
    output w m = canonicalTriple p (w.A + m.1 * p.delta) (w.B + m.2 * p.delta) := by
  exact Triple.ext rfl rfl (output_canonical_c w m)

/-- Bijective translation of the complete field-mask alphabet. -/
def maskTransport {F : Type*} [Field F] {p : Setup F}
    (w₁ w₂ : WitnessOffsets p) : (F × F) ≃ (F × F) where
  toFun m := (m.1 + (w₁.A - w₂.A) / p.delta, m.2 + (w₁.B - w₂.B) / p.delta)
  invFun m := (m.1 - (w₁.A - w₂.A) / p.delta, m.2 - (w₁.B - w₂.B) / p.delta)
  left_inv m := by apply Prod.ext <;> simp
  right_inv m := by apply Prod.ext <;> simp

theorem transport_preserves_output {F : Type*} [Field F] {p : Setup F}
    (w₁ w₂ : WitnessOffsets p) (m : F × F) :
    output w₂ (maskTransport w₁ w₂ m) = output w₁ m := by
  have ha : w₂.A + (m.1 + (w₁.A - w₂.A) / p.delta) * p.delta = w₁.A + m.1 * p.delta := by
    field_simp [p.delta_ne_zero]
    ring
  have hb : w₂.B + (m.2 + (w₁.B - w₂.B) / p.delta) * p.delta = w₁.B + m.2 * p.delta := by
    field_simp [p.delta_ne_zero]
    ring
  rw [output_eq_canonical, output_eq_canonical]
  change canonicalTriple p (w₂.A + (m.1 + (w₁.A - w₂.A) / p.delta) * p.delta)
    (w₂.B + (m.2 + (w₁.B - w₂.B) / p.delta) * p.delta) = _
  rw [ha, hb]

noncomputable def fullEventCount {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (event : Triple F → Prop) : Nat := by
  classical
  exact Fintype.card {m : F × F // event (output w m)}

/-- Any deterministic event of the ideal triple has the same exact count
under full-field uniform masks for any two compatible witness offsets. -/
theorem full_event_counts_equal {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (event : Triple F → Prop) :
    fullEventCount w₁ event = fullEventCount w₂ event := by
  classical
  apply Fintype.card_congr
  exact (maskTransport w₁ w₂).subtypeEquiv (by
    intro m
    rw [transport_preserves_output])

theorem full_observation_counts_equal {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop) :
    fullEventCount w₁ (event ∘ observe) = fullEventCount w₂ (event ∘ observe) :=
  full_event_counts_equal w₁ w₂ (event ∘ observe)

/-- Failure remains an observed outcome; it is not conditioned away. This
also covers any triple-determined infinity rejection or encoding failure. -/
theorem full_failure_counts_equal {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (observe : Triple F → Option Ω) :
    fullEventCount w₁ (fun triple => observe triple = none) =
      fullEventCount w₂ (fun triple => observe triple = none) :=
  full_event_counts_equal w₁ w₂ _

noncomputable def nonzeroValues (F : Type*) [Field F] [Fintype F] : Finset F := by
  classical
  exact Finset.univ.erase 0

noncomputable def nonzeroMasks (F : Type*) [Field F] [Fintype F] : Finset (F × F) :=
  (nonzeroValues F).product (nonzeroValues F)

noncomputable def badMasks (F : Type*) [Field F] [Fintype F] : Finset (F × F) := by
  classical
  exact Finset.univ \ nonzeroMasks F

noncomputable def nonzeroEventCount {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (event : Triple F → Prop) : Nat := by
  classical
  exact ((nonzeroMasks F).filter (fun m => event (output w m))).card

theorem nonzero_masks_card (F : Type*) [Field F] [Fintype F] :
    (nonzeroMasks F).card = (Fintype.card F - 1) ^ 2 := by
  classical
  simp [nonzeroMasks, nonzeroValues, Finset.card_product, pow_two]

theorem nonzero_masks_positive (F : Type*) [Field F] [Fintype F] :
    0 < (nonzeroMasks F).card := by
  rw [nonzero_masks_card]
  exact pow_pos (by have := Fintype.one_lt_card (α := F); omega) _

theorem bad_masks_card_bound (F : Type*) [Field F] [Fintype F] :
    (badMasks F).card ≤ 2 * Fintype.card F := by
  classical
  have contained : badMasks F ⊆
      (({0} : Finset F).product Finset.univ) ∪ (Finset.univ.product ({0} : Finset F)) := by
    intro m member
    rcases m with ⟨r, s⟩
    by_cases hr : r = 0
    · subst r
      simp
    · have hs : s = 0 := by
        simpa [badMasks, nonzeroMasks, nonzeroValues, hr] using member
      subst s
      simp
  calc
    _ ≤ ((({0} : Finset F).product Finset.univ) ∪ (Finset.univ.product ({0} : Finset F))).card :=
      Finset.card_le_card contained
    _ ≤ (({0} : Finset F).product Finset.univ).card +
        (Finset.univ.product ({0} : Finset F)).card := Finset.card_union_le _ _
    _ = _ := by simp; omega

theorem full_count_eq_filter {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (event : Triple F → Prop) :
    fullEventCount w event = (Finset.univ.filter (fun m => event (output w m))).card := by
  classical
  exact Fintype.card_subtype _

theorem nonzero_count_le_full {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (event : Triple F → Prop) :
    nonzeroEventCount w event ≤ fullEventCount w event := by
  classical
  rw [full_count_eq_filter]
  apply Finset.card_le_card
  intro m member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
  exact member.2

theorem full_count_le_nonzero_add_bad {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (event : Triple F → Prop) :
    fullEventCount w event ≤ nonzeroEventCount w event + (badMasks F).card := by
  classical
  rw [full_count_eq_filter]
  have contained : Finset.univ.filter (fun m => event (output w m)) ⊆
      (nonzeroMasks F).filter (fun m => event (output w m)) ∪ badMasks F := by
    intro m member
    by_cases good : m ∈ nonzeroMasks F
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨good, (Finset.mem_filter.mp member).2⟩)
    · exact Finset.mem_union_right _ (by simp [badMasks, good])
  exact (Finset.card_le_card contained).trans (Finset.card_union_le _ _)

/-- Removing zero masks changes event counts by at most two field rows. -/
theorem nonzero_event_count_bound {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (event : Triple F → Prop) :
    nonzeroEventCount w₁ event ≤ nonzeroEventCount w₂ event + 2 * Fintype.card F ∧
    nonzeroEventCount w₂ event ≤ nonzeroEventCount w₁ event + 2 * Fintype.card F := by
  have same := full_event_counts_equal w₁ w₂ event
  have a := nonzero_count_le_full w₁ event
  have b := nonzero_count_le_full w₂ event
  have c := full_count_le_nonzero_add_bad w₁ event
  have d := full_count_le_nonzero_add_bad w₂ event
  have bad := bad_masks_card_bound F
  omega

noncomputable def nonzeroEventProbability {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (event : Triple F → Prop) : ℚ :=
  (nonzeroEventCount w event : ℚ) / (nonzeroMasks F).card

theorem nonzero_probability_bound {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (event : Triple F → Prop) :
    |nonzeroEventProbability w₁ event - nonzeroEventProbability w₂ event| ≤
      (2 * (Fintype.card F : ℚ)) / (nonzeroMasks F).card := by
  have count := nonzero_event_count_bound w₁ w₂ event
  have upper : (nonzeroEventCount w₁ event : ℚ) ≤ nonzeroEventCount w₂ event + 2 * Fintype.card F := by
    exact_mod_cast count.1
  have lower : (nonzeroEventCount w₂ event : ℚ) ≤ nonzeroEventCount w₁ event + 2 * Fintype.card F := by
    exact_mod_cast count.2
  have positive : (0 : ℚ) < (nonzeroMasks F).card := by exact_mod_cast nonzero_masks_positive F
  unfold nonzeroEventProbability
  rw [← sub_div]
  apply abs_le.mpr
  constructor
  · rw [← neg_div]
    exact (div_le_div_iff_of_pos_right positive).2 (by linarith)
  · exact (div_le_div_iff_of_pos_right positive).2 (by linarith)

/-- An explicit event-distance bound for nonzero masks. This deliberately
does not assert equality of the nonzero-mask distributions. -/
theorem nonzero_probability_explicit_bound {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (event : Triple F → Prop) :
    |nonzeroEventProbability w₁ event - nonzeroEventProbability w₂ event| ≤
      (4 * (Fintype.card F : ℚ)) / ((Fintype.card F : ℚ) - 1) ^ 2 := by
  have cardinal : 1 ≤ Fintype.card F := by have := Fintype.one_lt_card (α := F); omega
  have shape : ((nonzeroMasks F).card : ℚ) = ((Fintype.card F : ℚ) - 1) ^ 2 := by
    rw [nonzero_masks_card]
    simp only [Nat.cast_pow, Nat.cast_sub cardinal, Nat.cast_one]
  have positive : (0 : ℚ) < (nonzeroMasks F).card := by exact_mod_cast nonzero_masks_positive F
  rw [← shape]
  exact (nonzero_probability_bound w₁ w₂ event).trans
    ((div_le_div_iff_of_pos_right positive).2 (by
      have nonneg : (0 : ℚ) ≤ Fintype.card F := Nat.cast_nonneg _
      linarith))

theorem nonzero_observation_bound {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop) :
    |nonzeroEventProbability w₁ (event ∘ observe) - nonzeroEventProbability w₂ (event ∘ observe)| ≤
      (4 * (Fintype.card F : ℚ)) / ((Fintype.card F : ℚ) - 1) ^ 2 :=
  nonzero_probability_explicit_bound w₁ w₂ (event ∘ observe)

/-! ## Explicit bounded-retry count model

This ideal model has `accepted` equally likely accepted labels, one draw label
per accepted value, and `rejected` retry labels. A complete attempt tape has
`(accepted + rejected)^attempts` equally likely words. The recurrence counts
all suffix words after the first accepted label. This is a mathematical draw
alphabet model, not a claimed coupling to the application byte sampler.
-/

/-- Number of complete attempt tapes yielding one specified accepted label. -/
def perValueWeight (accepted rejected : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (accepted + rejected) ^ n + rejected * perValueWeight accepted rejected n

/-- Every tape either fails all attempts or yields exactly one accepted label. -/
theorem scalar_retry_normalization (accepted rejected attempts : Nat) :
    accepted * perValueWeight accepted rejected attempts + rejected ^ attempts =
      (accepted + rejected) ^ attempts := by
  induction attempts with
  | zero => simp [perValueWeight]
  | succ n ih =>
    simp only [perValueWeight, pow_succ]
    calc
      _ = accepted * (accepted + rejected) ^ n +
          rejected * (accepted * perValueWeight accepted rejected n + rejected ^ n) := by ring
      _ = _ := by rw [ih]; ring

/-- A pair runs the same finite retry policy independently for both masks. -/
def retryPairTotal (accepted rejected attempts : Nat) : Nat :=
  ((accepted + rejected) ^ attempts) ^ 2

def retryPairSuccess (accepted rejected attempts : Nat) : Nat :=
  accepted ^ 2 * (perValueWeight accepted rejected attempts) ^ 2

def retryPairFailure (accepted rejected attempts : Nat) : Nat :=
  retryPairTotal accepted rejected attempts - retryPairSuccess accepted rejected attempts

theorem retry_pair_success_le_total (accepted rejected attempts : Nat) :
    retryPairSuccess accepted rejected attempts ≤ retryPairTotal accepted rejected attempts := by
  have bound : accepted * perValueWeight accepted rejected attempts ≤
      (accepted + rejected) ^ attempts := by
    have := scalar_retry_normalization accepted rejected attempts
    omega
  have square := Nat.mul_self_le_mul_self bound
  simpa [retryPairSuccess, retryPairTotal, pow_two, mul_assoc, mul_left_comm, mul_comm] using square

theorem retry_pair_normalization (accepted rejected attempts : Nat) :
    retryPairFailure accepted rejected attempts + retryPairSuccess accepted rejected attempts =
      retryPairTotal accepted rejected attempts := by
  exact Nat.sub_add_cancel (retry_pair_success_le_total accepted rejected attempts)

theorem retry_pair_total_positive {accepted : Nat} (positive : 0 < accepted)
    (rejected attempts : Nat) : 0 < retryPairTotal accepted rejected attempts := by
  unfold retryPairTotal
  exact pow_pos (pow_pos (by omega) _) _

/-- Retains the common retry failure outcome in the observed event count.
An observer can additionally fail or reject a successful triple; it is still
applied to the triple without conditioning. -/
noncomputable def boundedEventCount {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) : Nat :=
  (if event failure then retryPairFailure (Fintype.card F - 1) rejected attempts else 0) +
    (perValueWeight (Fintype.card F - 1) rejected attempts) ^ 2 *
      nonzeroEventCount w (event ∘ observe)

noncomputable def boundedEventProbability {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) : ℚ :=
  (boundedEventCount w observe event failure rejected attempts : ℚ) /
    retryPairTotal (Fintype.card F - 1) rejected attempts

noncomputable def retrySuccessProbability (F : Type*) [Field F] [Fintype F]
    (rejected attempts : Nat) : ℚ :=
  (retryPairSuccess (Fintype.card F - 1) rejected attempts : ℚ) /
    retryPairTotal (Fintype.card F - 1) rejected attempts

noncomputable def retryFailureProbability (F : Type*) [Field F] [Fintype F]
    (rejected attempts : Nat) : ℚ :=
  (retryPairFailure (Fintype.card F - 1) rejected attempts : ℚ) /
    retryPairTotal (Fintype.card F - 1) rejected attempts

theorem nonzero_count_true {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) :
    nonzeroEventCount w (fun _ => True) = (nonzeroMasks F).card := by
  classical
  simp [nonzeroEventCount]

theorem nonzero_count_le_total {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (event : Triple F → Prop) :
    nonzeroEventCount w event ≤ (nonzeroMasks F).card :=
  Finset.card_filter_le _ _

theorem bounded_count_true {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (failure : Ω)
    (rejected attempts : Nat) :
    boundedEventCount w observe (fun _ => True) failure rejected attempts =
      retryPairTotal (Fintype.card F - 1) rejected attempts := by
  simp only [boundedEventCount, if_true, Function.comp_def, nonzero_count_true, nonzero_masks_card]
  rw [Nat.mul_comm]
  exact retry_pair_normalization _ _ _

theorem bounded_count_le_total {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) :
    boundedEventCount w observe event failure rejected attempts ≤
      retryPairTotal (Fintype.card F - 1) rejected attempts := by
  have count := nonzero_count_le_total w (event ∘ observe)
  rw [nonzero_masks_card] at count
  have bound := Nat.mul_le_mul_left ((perValueWeight (Fintype.card F - 1) rejected attempts) ^ 2) count
  have normalized := retry_pair_normalization (Fintype.card F - 1) rejected attempts
  unfold boundedEventCount
  split_ifs <;> dsimp [retryPairSuccess] at normalized <;> nlinarith

theorem retry_probabilities_normalized (F : Type*) [Field F] [Fintype F]
    (rejected attempts : Nat) :
    retryFailureProbability F rejected attempts + retrySuccessProbability F rejected attempts = 1 := by
  have cardinal : 0 < Fintype.card F - 1 := by have := Fintype.one_lt_card (α := F); omega
  have pos : (0 : ℚ) < retryPairTotal (Fintype.card F - 1) rejected attempts := by
    exact_mod_cast retry_pair_total_positive cardinal rejected attempts
  unfold retryFailureProbability retrySuccessProbability
  rw [← add_div]
  have normalization : (retryPairFailure (Fintype.card F - 1) rejected attempts : ℚ) +
      retryPairSuccess (Fintype.card F - 1) rejected attempts =
      retryPairTotal (Fintype.card F - 1) rejected attempts := by
    exact_mod_cast retry_pair_normalization (Fintype.card F - 1) rejected attempts
  rw [normalization, div_self (ne_of_gt pos)]

theorem retry_success_probability_bounds (F : Type*) [Field F] [Fintype F]
    (rejected attempts : Nat) :
    0 ≤ retrySuccessProbability F rejected attempts ∧ retrySuccessProbability F rejected attempts ≤ 1 := by
  have cardinal : 0 < Fintype.card F - 1 := by have := Fintype.one_lt_card (α := F); omega
  have positive : (0 : ℚ) < retryPairTotal (Fintype.card F - 1) rejected attempts := by
    exact_mod_cast retry_pair_total_positive cardinal rejected attempts
  unfold retrySuccessProbability
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt positive)
  · apply (div_le_iff₀ positive).2
    simp only [one_mul]
    exact_mod_cast retry_pair_success_le_total (Fintype.card F - 1) rejected attempts

/-- Exact unconditioned decomposition: the common retry-failure mass is
included even when the observer's event accepts the failure outcome. -/
theorem bounded_probability_mixture {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) :
    boundedEventProbability w observe event failure rejected attempts =
      retryFailureProbability F rejected attempts * (if event failure then 1 else 0) +
      retrySuccessProbability F rejected attempts * nonzeroEventProbability w (event ∘ observe) := by
  have maskspos : (0 : ℚ) < (nonzeroMasks F).card := by exact_mod_cast nonzero_masks_positive F
  have shapemasks : ((nonzeroMasks F).card : ℚ) = ((Fintype.card F - 1 : Nat) : ℚ) ^ 2 := by
    rw [nonzero_masks_card, Nat.cast_pow]
  unfold boundedEventProbability boundedEventCount retryFailureProbability
    retrySuccessProbability nonzeroEventProbability retryPairSuccess
  push_cast
  rw [← shapemasks]
  split_ifs <;> field_simp
  all_goals simp

/-- A common bounded retry policy cannot enlarge the ideal nonzero-mask
observation distance. This includes every retry failure, not only successful
proofs, in the event probability. -/
theorem bounded_probability_difference {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) :
    boundedEventProbability w₁ observe event failure rejected attempts -
      boundedEventProbability w₂ observe event failure rejected attempts =
      retrySuccessProbability F rejected attempts *
        (nonzeroEventProbability w₁ (event ∘ observe) - nonzeroEventProbability w₂ (event ∘ observe)) := by
  rw [bounded_probability_mixture, bounded_probability_mixture]
  ring

/-- Explicit statistical event bound for the entire bounded-retry output,
including the common failure mass. No success conditioning is performed. -/
theorem bounded_observation_bound {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) :
    |boundedEventProbability w₁ observe event failure rejected attempts -
      boundedEventProbability w₂ observe event failure rejected attempts| ≤
      (4 * (Fintype.card F : ℚ)) / ((Fintype.card F : ℚ) - 1) ^ 2 := by
  have success := retry_success_probability_bounds F rejected attempts
  have eventbound := nonzero_observation_bound w₁ w₂ observe event
  have boundnonneg : (0 : ℚ) ≤
      (4 * (Fintype.card F : ℚ)) / ((Fintype.card F : ℚ) - 1) ^ 2 := by
    exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)
  rw [bounded_probability_difference]
  apply abs_le.mpr
  have eventbounds := abs_le.mp eventbound
  have upper := mul_le_mul_of_nonneg_left eventbounds.2 success.1
  have lower := mul_le_mul_of_nonneg_left eventbounds.1 success.1
  have mass := mul_le_mul_of_nonneg_right success.2 boundnonneg
  constructor <;> nlinarith

/-- The zero-attempt edge case has probability one of the explicit common
failure observation, so it is also covered without a conditioning exception. -/
theorem bounded_zero_attempts {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected : Nat) :
    boundedEventProbability w observe event failure rejected 0 =
      (if event failure then 1 else 0) := by
  simp [boundedEventProbability, boundedEventCount, perValueWeight,
    retryPairTotal, retryPairFailure, retryPairSuccess]

/-! ## Executable finite attempt tapes

The following sampler makes the preceding retry counts concrete. At each
node it either accepts a value or consumes a retry label. A suffix after an
acceptance is present in the tape but deliberately unobserved. -/

universe u v

def AttemptTape (A : Type u) (R : Type v) : Nat → Type (max u v)
  | 0 => PUnit
  | n + 1 => (A × AttemptTape A R n) ⊕ (R × AttemptTape A R n)

instance attemptTapeFintype (A R : Type*) [Fintype A] [Fintype R] (n : Nat) :
    Fintype (AttemptTape A R n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((A × AttemptTape A R n) ⊕ (R × AttemptTape A R n)))

def sampleTape {A R : Type*} : {n : Nat} → AttemptTape A R n → Option A
  | 0, _ => none
  | _ + 1, .inl (a, _) => some a
  | _ + 1, .inr (_, rest) => sampleTape rest

theorem attempt_tape_card (A R : Type*) [Fintype A] [Fintype R] (n : Nat) :
    Fintype.card (AttemptTape A R n) = (Fintype.card A + Fintype.card R) ^ n := by
  induction n with
  | zero => simp [AttemptTape]
  | succ n ih =>
    change Fintype.card ((A × AttemptTape A R n) ⊕ (R × AttemptTape A R n)) = _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, ih, pow_succ]
    ring

/-- One-step equivalence for tapes yielding a specified accepted value. -/
def successTapeEquiv (A R : Type*) (n : Nat) (a : A) :
    {t : AttemptTape A R (n + 1) // sampleTape t = some a} ≃
      AttemptTape A R n ⊕ (R × {t : AttemptTape A R n // sampleTape t = some a}) where
  toFun t := match t with
    | ⟨.inl (_, rest), _⟩ => .inl rest
    | ⟨.inr (retry, rest), accepted⟩ => .inr (retry, ⟨rest, accepted⟩)
  invFun t := match t with
    | .inl rest => ⟨.inl (a, rest), rfl⟩
    | .inr (retry, rest) => ⟨.inr (retry, rest.val), rest.property⟩
  left_inv := by
    intro t
    rcases t with ⟨t, h⟩
    cases t with
    | inl x =>
      rcases x with ⟨b, rest⟩
      have same : b = a := Option.some.inj h
      subst b
      rfl
    | inr x => rfl
  right_inv := by
    intro t
    cases t <;> rfl

/-- The success multiplicity is the same for every accepted value, proved
from the actual finite sampler rather than assumed in its probability law. -/
theorem sample_tape_success_count (A R : Type*) [Fintype A] [Fintype R] (n : Nat) (a : A) :
    Fintype.card {t : AttemptTape A R n // sampleTape t = some a} =
      perValueWeight (Fintype.card A) (Fintype.card R) n := by
  classical
  induction n with
  | zero => simp [AttemptTape, sampleTape, perValueWeight]
  | succ n ih =>
    rw [Fintype.card_congr (successTapeEquiv A R n a), Fintype.card_sum,
      Fintype.card_prod, attempt_tape_card, ih]
    rfl

def failureTapeEquiv (A R : Type*) (n : Nat) :
    {t : AttemptTape A R (n + 1) // sampleTape t = none} ≃
      R × {t : AttemptTape A R n // sampleTape t = none} where
  toFun t := match t with
    | ⟨.inl _, h⟩ => by cases h
    | ⟨.inr (retry, rest), h⟩ => (retry, ⟨rest, h⟩)
  invFun t := ⟨.inr (t.1, t.2.val), t.2.property⟩
  left_inv := by
    intro t
    rcases t with ⟨t, h⟩
    cases t with
    | inl x => cases h
    | inr x => rfl
  right_inv _ := rfl

theorem sample_tape_failure_count (A R : Type*) [Fintype A] [Fintype R] (n : Nat) :
    Fintype.card {t : AttemptTape A R n // sampleTape t = none} = (Fintype.card R) ^ n := by
  classical
  induction n with
  | zero => simp [AttemptTape, sampleTape]
  | succ n ih =>
    rw [Fintype.card_congr (failureTapeEquiv A R n), Fintype.card_prod, ih, pow_succ]
    ring

/-- The two-mask sampler. A failure of either independent bounded tape is
observable as `none`; successful masks are never silently renormalized. -/
def samplePair {A R : Type*} {n : Nat} (t : AttemptTape A R n × AttemptTape A R n) :
    Option (A × A) :=
  match sampleTape (R := R) t.1, sampleTape (R := R) t.2 with
  | some r, some s => some (r, s)
  | _, _ => none

def pairSuccessTapeEquiv (A R : Type*) (n : Nat) (a b : A) :
    {t : AttemptTape A R n × AttemptTape A R n // samplePair t = some (a, b)} ≃
      {t : AttemptTape A R n // sampleTape (R := R) t = some a} ×
      {t : AttemptTape A R n // sampleTape (R := R) t = some b} where
  toFun t := by
    have both : sampleTape (R := R) t.val.1 = some a ∧
        sampleTape (R := R) t.val.2 = some b := by
      have h := t.property
      cases first : sampleTape (R := R) t.val.1 <;>
        cases second : sampleTape (R := R) t.val.2 <;> simp_all [samplePair]
    exact (⟨t.val.1, both.1⟩, ⟨t.val.2, both.2⟩)
  invFun t := ⟨(t.1.val, t.2.val), by
    change (match sampleTape (R := R) t.1.val, sampleTape (R := R) t.2.val with
      | some r, some s => some (r, s)
      | _, _ => none) = some (a, b)
    rw [t.1.property, t.2.property]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sample_pair_success_count (A R : Type*) [Fintype A] [Fintype R] (n : Nat) (a b : A) :
    Nat.card {t : AttemptTape A R n × AttemptTape A R n // samplePair t = some (a, b)} =
      (perValueWeight (Fintype.card A) (Fintype.card R) n) ^ 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (pairSuccessTapeEquiv A R n a b), Fintype.card_prod,
    sample_tape_success_count, sample_tape_success_count, pow_two]

/-- Partition the observed event into the explicit failure fiber and one
fiber for each successful value. This equivalence does not discard failure. -/
noncomputable def observedFiberEquiv {X Y Ω : Type*} (f : X → Option Y) (observe : Y → Ω)
    (failure : Ω) (event : Ω → Prop) :
    {x : X // event ((f x).elim failure observe)} ≃
      {x : X // f x = none ∧ event failure} ⊕
      (Σ y : {y : Y // event (observe y)}, {x : X // f x = some y.val}) := by
  let join : ({x : X // f x = none ∧ event failure} ⊕
      (Σ y : {y : Y // event (observe y)}, {x : X // f x = some y.val})) →
      {x : X // event ((f x).elim failure observe)} := fun input => match input with
    | .inl t => ⟨t.val, by simpa [t.property.1] using t.property.2⟩
    | .inr ⟨y, t⟩ => ⟨t.val, by simpa [t.property] using y.property⟩
  apply (Equiv.ofBijective join ?_).symm
  constructor
  · intro x y same
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        have values : a.val = b.val := by
          simpa only [join] using congrArg (fun z : {x : X // event ((f x).elim failure observe)} => z.val) same
        exact congrArg Sum.inl (Subtype.ext values)
      | inr b =>
        rcases b with ⟨v, b⟩
        have values : a.val = b.val := by
          simpa only [join] using congrArg (fun z : {x : X // event ((f x).elim failure observe)} => z.val) same
        have bad := a.property.1
        rw [values, b.property] at bad
        cases bad
    | inr a =>
      rcases a with ⟨v, a⟩
      cases y with
      | inl b =>
        have values : a.val = b.val := by
          simpa only [join] using congrArg (fun z : {x : X // event ((f x).elim failure observe)} => z.val) same
        have bad := a.property
        rw [values, b.property.1] at bad
        cases bad
      | inr b =>
        rcases b with ⟨w, b⟩
        have values : a.val = b.val := by
          simpa only [join] using congrArg (fun z : {x : X // event ((f x).elim failure observe)} => z.val) same
        have outputs : v.val = w.val :=
          Option.some.inj (a.property.symm.trans ((congrArg f values).trans b.property))
        have vw : v = w := Subtype.ext outputs
        subst w
        exact congrArg Sum.inr (congrArg (Sigma.mk v) (Subtype.ext values))
  · intro x
    cases h : f x.val with
    | none =>
      exact ⟨.inl ⟨x.val, h, by simpa [h] using x.property⟩, rfl⟩
    | some y =>
      exact ⟨.inr ⟨⟨y, by simpa [h] using x.property⟩, ⟨x.val, h⟩⟩, rfl⟩

/-- Uniform success fibers give an exact count for any deterministic
observation, with the entire failure fiber included. -/
theorem observed_fiber_count {X Y Ω : Type*} [Fintype X] [Fintype Y]
    (f : X → Option Y) (observe : Y → Ω) (failure : Ω) (event : Ω → Prop)
    (weight : Nat) (uniform : ∀ y, Nat.card {x : X // f x = some y} = weight) :
    Nat.card {x : X // event ((f x).elim failure observe)} =
      (if event failure then Nat.card {x : X // f x = none} else 0) +
      Nat.card {y : Y // event (observe y)} * weight := by
  classical
  simp only [Nat.card_eq_fintype_card] at uniform ⊢
  rw [Fintype.card_congr (observedFiberEquiv f observe failure event),
    Fintype.card_sum, Fintype.card_sigma]
  simp_rw [uniform]
  by_cases acceptedFailure : event failure <;> simp [acceptedFailure]

/-- Every pair tape either yields a pair or fails; together with the proved
uniform success fibers this identifies the exact failure multiplicity. -/
theorem sample_pair_failure_count (A R : Type*) [Fintype A] [Fintype R] (n : Nat) :
    Nat.card {t : AttemptTape A R n × AttemptTape A R n // samplePair t = none} =
      retryPairFailure (Fintype.card A) (Fintype.card R) n := by
  classical
  have partition := observed_fiber_count (@samplePair A R n) (fun _ => ()) () (fun _ => True)
    ((perValueWeight (Fintype.card A) (Fintype.card R) n) ^ 2)
    (fun y => sample_pair_success_count A R n y.1 y.2)
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_true, if_true, Fintype.card_prod,
    attempt_tape_card, ← pow_two] at partition
  rw [Nat.card_eq_fintype_card]
  unfold retryPairFailure retryPairTotal retryPairSuccess
  omega

/-- Exact event-count law for the concrete finite pair sampler. -/
theorem sample_pair_observed_count {A R Ω : Type*} [Fintype A] [Fintype R]
    (n : Nat) (observe : A × A → Ω) (failure : Ω) (event : Ω → Prop) :
    Nat.card {t : AttemptTape A R n × AttemptTape A R n //
      event ((samplePair t).elim failure observe)} =
      (if event failure then retryPairFailure (Fintype.card A) (Fintype.card R) n else 0) +
      Nat.card {y : A × A // event (observe y)} *
        (perValueWeight (Fintype.card A) (Fintype.card R) n) ^ 2 := by
  rw [observed_fiber_count _ _ _ _ _ (fun y => sample_pair_success_count A R n y.1 y.2),
    sample_pair_failure_count]

abbrev NonzeroFieldValue (F : Type*) [Field F] := {x : F // x ≠ 0}

theorem nonzero_field_values_card (F : Type*) [Field F] [Fintype F] :
    Fintype.card (NonzeroFieldValue F) = Fintype.card F - 1 := by
  classical
  simp [NonzeroFieldValue, Fintype.card_subtype_compl]

/-- The field event count uses all ordered pairs of nonzero values exactly
once. The equivalence exposes their actual field projections. -/
theorem nonzero_pair_event_count {F : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (event : Triple F → Prop) :
    Nat.card {ab : NonzeroFieldValue F × NonzeroFieldValue F //
      event (output w (ab.1.val, ab.2.val))} = nonzeroEventCount w event := by
  classical
  let e : {ab : NonzeroFieldValue F × NonzeroFieldValue F //
      event (output w (ab.1.val, ab.2.val))} ≃
      {m : F × F // m ∈ nonzeroMasks F ∧ event (output w m)} := {
    toFun := fun ab => ⟨(ab.val.1.val, ab.val.2.val),
      by simpa [nonzeroMasks, nonzeroValues] using
        And.intro (And.intro ab.val.1.property ab.val.2.property) ab.property⟩
    invFun := fun m => ⟨(⟨m.val.1, by
        have := m.property.1
        simp [nonzeroMasks, nonzeroValues] at this
        exact this.1⟩, ⟨m.val.2, by
        have := m.property.1
        simp [nonzeroMasks, nonzeroValues] at this
        exact this.2⟩), m.property.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold nonzeroEventCount
  congr 1
  ext m
  simp

/-- Fully enumerated ideal attempt tapes, retaining retry exhaustion and
all deterministic observer failures as output values. -/
def finiteObservedOutput {F Ω : Type*} [Field F] {p : Setup F}
    (w : WitnessOffsets p) (observe : Triple F → Ω) (failure : Ω)
    {rejected attempts : Nat}
    (t : AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts ×
      AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts) : Ω :=
  (samplePair t).elim failure (fun ab => observe (output w (ab.1.val, ab.2.val)))

/-- The abstract count law above is exactly the cardinality of an event of
the concrete, executable finite sampler. It is not a stipulated probability. -/
theorem finite_bounded_event_counts {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) :
    Nat.card {t : AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts ×
      AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts //
      event (finiteObservedOutput w observe failure t)} =
      boundedEventCount w observe event failure rejected attempts := by
  classical
  unfold finiteObservedOutput
  rw [sample_pair_observed_count]
  rw [nonzero_field_values_card, Fintype.card_fin]
  have count := nonzero_pair_event_count w (event ∘ observe)
  have equality := congrArg (fun k =>
    (if event failure then retryPairFailure (Fintype.card F - 1) rejected attempts else 0) +
      k * (perValueWeight (Fintype.card F - 1) rejected attempts) ^ 2) count
  exact equality.trans (by unfold boundedEventCount; rw [Nat.mul_comm])

theorem finite_attempt_pairs_card (F : Type*) [Field F] [Fintype F]
    (rejected attempts : Nat) :
    Nat.card (AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts ×
      AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts) =
      retryPairTotal (Fintype.card F - 1) rejected attempts := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, attempt_tape_card,
    nonzero_field_values_card, Fintype.card_fin, retryPairTotal, pow_two]

/-- Probability of a finite-tape observation event, with the complete tape
space as denominator rather than the successful-output subspace. -/
noncomputable def finiteEventProbability {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) : ℚ :=
  (Nat.card {t : AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts ×
    AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts //
    event (finiteObservedOutput w observe failure t)} : ℚ) /
  Nat.card (AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts ×
    AttemptTape (NonzeroFieldValue F) (Fin rejected) attempts)

theorem finite_probability_eq_bounded {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) :
    finiteEventProbability w observe event failure rejected attempts =
      boundedEventProbability w observe event failure rejected attempts := by
  rw [finiteEventProbability, finite_bounded_event_counts, finite_attempt_pairs_card]
  rfl

theorem finite_observation_bound {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w₁ w₂ : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (rejected attempts : Nat) :
    |finiteEventProbability w₁ observe event failure rejected attempts -
      finiteEventProbability w₂ observe event failure rejected attempts| ≤
      (4 * (Fintype.card F : ℚ)) / ((Fintype.card F : ℚ) - 1) ^ 2 := by
  rw [finite_probability_eq_bounded, finite_probability_eq_bounded]
  exact bounded_observation_bound w₁ w₂ observe event failure rejected attempts

end IdealGroth16

#print axioms IdealGroth16.Triple.ext
#print axioms IdealGroth16.output_canonical_c
#print axioms IdealGroth16.output_eq_canonical
#print axioms IdealGroth16.transport_preserves_output
#print axioms IdealGroth16.full_event_counts_equal
#print axioms IdealGroth16.full_observation_counts_equal
#print axioms IdealGroth16.full_failure_counts_equal
#print axioms IdealGroth16.nonzero_masks_card
#print axioms IdealGroth16.nonzero_masks_positive
#print axioms IdealGroth16.bad_masks_card_bound
#print axioms IdealGroth16.full_count_eq_filter
#print axioms IdealGroth16.nonzero_count_le_full
#print axioms IdealGroth16.full_count_le_nonzero_add_bad
#print axioms IdealGroth16.nonzero_event_count_bound
#print axioms IdealGroth16.nonzero_probability_bound
#print axioms IdealGroth16.nonzero_probability_explicit_bound
#print axioms IdealGroth16.nonzero_observation_bound
#print axioms IdealGroth16.scalar_retry_normalization
#print axioms IdealGroth16.retry_pair_success_le_total
#print axioms IdealGroth16.retry_pair_normalization
#print axioms IdealGroth16.retry_pair_total_positive
#print axioms IdealGroth16.nonzero_count_true
#print axioms IdealGroth16.nonzero_count_le_total
#print axioms IdealGroth16.bounded_count_true
#print axioms IdealGroth16.bounded_count_le_total
#print axioms IdealGroth16.retry_probabilities_normalized
#print axioms IdealGroth16.retry_success_probability_bounds
#print axioms IdealGroth16.bounded_probability_mixture
#print axioms IdealGroth16.bounded_probability_difference
#print axioms IdealGroth16.bounded_observation_bound
#print axioms IdealGroth16.bounded_zero_attempts
#print axioms IdealGroth16.attempt_tape_card
#print axioms IdealGroth16.sample_tape_success_count
#print axioms IdealGroth16.sample_tape_failure_count
#print axioms IdealGroth16.sample_pair_success_count
#print axioms IdealGroth16.observed_fiber_count
#print axioms IdealGroth16.sample_pair_failure_count
#print axioms IdealGroth16.sample_pair_observed_count
#print axioms IdealGroth16.nonzero_field_values_card
#print axioms IdealGroth16.nonzero_pair_event_count
#print axioms IdealGroth16.finite_bounded_event_counts
#print axioms IdealGroth16.finite_attempt_pairs_card
#print axioms IdealGroth16.finite_probability_eq_bounded
#print axioms IdealGroth16.finite_observation_bound
