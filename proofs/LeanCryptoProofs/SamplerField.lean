import LeanCryptoProofs.FrModel
import LeanCryptoProofs.Groth16SharedSamplerBridge
import LeanCrypto.Probability.ByteEntropy
import Mathlib.Algebra.BigOperators.Fin

/-! Exact representation and event-count transport for the actual shared
pure bounded sampler. OS entropy, the worker program, native proof points,
and release observations remain outside this module. -/
set_option autoImplicit false

namespace LeanCrypto.Proofs.SamplerField

attribute [local instance] Classical.propDecidable

open LeanCrypto.Sampling LeanCrypto.Probability.Rejection LeanCrypto.Proofs.BN254Fr
open scoped BigOperators

abbrev NonzeroField := {x : ZMod Q // x ≠ 0}

theorem scalar_ext {left right : Scalar} (equal : left.value = right.value) : left = right := by
  cases left
  cases right
  cases equal
  rfl

theorem scalar_model_nonzero (scalar : Scalar) : model scalar.value ≠ 0 := by
  intro zero
  have native := (model_zero_iff scalar.value).1 zero
  rw [Nat.mod_eq_of_lt (show scalar.value < Q from scalar.canonical)] at native
  have positive := scalar.positive
  omega

def scalarFieldEquiv : Scalar ≃ NonzeroField where
  toFun scalar := ⟨model scalar.value, scalar_model_nonzero scalar⟩
  invFun field := ⟨field.val.val, ZMod.val_pos.mpr field.property, ZMod.val_lt field.val⟩
  left_inv scalar := by
    apply scalar_ext
    exact ZMod.val_natCast_of_lt scalar.canonical
  right_inv field := by
    apply Subtype.ext
    exact ZMod.natCast_zmod_val field.val

theorem scalar_field_value (scalar : Scalar) :
    (scalarFieldEquiv scalar).val = model scalar.value := rfl

theorem field_scalar_value (field : NonzeroField) :
    (scalarFieldEquiv.symm field).value = field.val.val := rfl

def finScalarEquiv : Fin (Q - 1) ≃ Scalar where
  toFun index := ⟨index.val + 1, by omega, by
    change index.val + 1 < Q
    have := index.isLt
    omega⟩
  invFun scalar := ⟨scalar.value - 1, by
    have := scalar.positive
    have canonical : scalar.value < Q := scalar.canonical
    omega⟩
  left_inv index := by
    apply Fin.ext
    simp
  right_inv scalar := by
    apply scalar_ext
    simp only []
    have := scalar.positive
    omega

def finFieldEquiv : Fin (Q - 1) ≃ NonzeroField := finScalarEquiv.trans scalarFieldEquiv

theorem fin_field_value (index : Fin (Q - 1)) :
    (finFieldEquiv index).val = model (index.val + 1) := rfl

/-- Canonical Nat admission is retained before casting: a nonzero residue
of an out-of-range Nat is still rejected by the actual runtime classifier. -/
theorem admitValue_field (value : Nat) :
    (admitValue value).map (fun scalar => (scalarFieldEquiv scalar).val) =
      if 0 < value ∧ value < Q then some (model value) else none := by
  unfold admitValue
  split <;> rename_i condition
  · have allowed : 0 < value ∧ value < Q := of_decide_eq_true condition
    simp [allowed, scalarFieldEquiv]
  · have rejected : ¬(0 < value ∧ value < Q) := by
      simpa only [admissible, decide_eq_true_eq] using condition
    simp [rejected]

/-- The actual full-width byte decoder and runtime admission, followed by
the proved representation map, construct this exact field observation. -/
theorem admitCandidate_field (bytes : ByteArray) (width : bytes.size = 32) :
    (admitCandidate bytes).map (fun result => result.map
      (fun scalar => (scalarFieldEquiv scalar).val)) =
      .ok (if 0 < LeanCrypto.FixedBytes.decode bytes ∧ LeanCrypto.FixedBytes.decode bytes < Q
        then some (model (LeanCrypto.FixedBytes.decode bytes)) else none) := by
  simp only [admitCandidate, width, ↓reduceIte, Except.map]
  rw [LeanCrypto.Probability.ByteEntropy.runtime_decoder, admitValue_field]

/-- Exact one-draw field-event count for the actual byte classifier and
Scalar representation, before any retry-loop interpretation is introduced. -/
theorem candidate_field_sum (event : Option (ZMod Q) → Nat) :
    LeanCrypto.Probability.ByteEntropy.sumBytes 32 (fun bytes => match
      (admitCandidate bytes).map (fun result => result.map
        (fun scalar => (scalarFieldEquiv scalar).val)) with
      | .error _ => 0
      | .ok result => event result) =
      sumTo (2 ^ 256) (fun value =>
        event (if 0 < value ∧ value < Q then some (model value) else none)) := by
  calc
    _ = LeanCrypto.Probability.ByteEntropy.sumBytes 32 (fun bytes =>
        event (if 0 < LeanCrypto.FixedBytes.decode bytes ∧ LeanCrypto.FixedBytes.decode bytes < Q
          then some (model (LeanCrypto.FixedBytes.decode bytes)) else none)) := by
      apply LeanCrypto.Probability.ByteEntropy.sumBytes_congr
      intro bytes width
      rw [admitCandidate_field bytes width]
    _ = _ := by
      rw [LeanCrypto.Probability.ByteEntropy.sumBytes_decode 32 (fun value =>
        event (if 0 < value ∧ value < Q then some (model value) else none)),
        LeanCrypto.Probability.ByteEntropy.uint256_radix]

theorem mass_event_formula (D q budget : Nat) (positive : 0 < q) (fits : q ≤ D)
    (event : Option Nat → Nat) :
    mass D q budget event = retryCount D q ^ budget * event none +
      successWeight D q budget * sumTo (q - 1) (fun i => event (some (i + 1))) := by
  induction budget with
  | zero => simp [mass, sampler, sampleLoop, DrawTree.count, successWeight]
  | succ budget ih =>
    rw [mass_succ D q budget event positive fits, ih]
    simp only [successWeight, Nat.pow_succ, retryCount]
    ring

theorem pair_event_formula_raw (D q budget : Nat) (positive : 0 < q) (fits : q ≤ D)
    (event : Option (Nat × Nat) → Nat) :
    pairMass D q budget event =
      retryCount D q ^ budget * (D ^ budget + (q - 1) * successWeight D q budget) * event none +
      successWeight D q budget ^ 2 * sumTo (q - 1) (fun i =>
        sumTo (q - 1) (fun j => event (some (i + 1, j + 1)))) := by
  have tail : ∀ r : Nat, DrawTree.Bounded budget
      ((sampler q budget).bind (fun s => .done (r, s))) := by
    intro r
    simpa using DrawTree.bounded_bind budget 0 (sampler q budget)
      (fun s => .done (r, s)) (sampler_bounded q budget) (fun _ => trivial)
  unfold pairMass
  rw [pairSampler_equation,
    DrawTree.count_bind D budget budget _ _ (sampler_bounded q budget) tail]
  change mass D q budget _ = _
  rw [mass_event_formula D q budget positive fits]
  have continuation (r : Nat) :
      DrawTree.count D budget ((sampler q budget).bind (fun s => .done (r, s))) event =
        retryCount D q ^ budget * event none + successWeight D q budget *
          sumTo (q - 1) (fun j => event (some (r, j + 1))) := by
    rw [DrawTree.count_map D budget _ _ (sampler_bounded q budget)]
    change mass D q budget _ = _
    exact mass_event_formula D q budget positive fits _
  simp only []
  simp_rw [continuation]
  rw [sumTo_add, sumTo_const, sumTo_scale]
  ring

theorem pair_event_formula (D q budget : Nat) (positive : 0 < q) (fits : q ≤ D)
    (event : Option (Nat × Nat) → Nat) :
    pairMass D q budget event = pairMass D q budget failureEvent * event none +
      successWeight D q budget ^ 2 * sumTo (q - 1) (fun i =>
        sumTo (q - 1) (fun j => event (some (i + 1, j + 1)))) := by
  have failure : pairMass D q budget failureEvent =
      retryCount D q ^ budget * (D ^ budget + (q - 1) * successWeight D q budget) := by
    rw [pair_event_formula_raw D q budget positive fits failureEvent]
    simp [failureEvent, sumTo_const]
  rw [pair_event_formula_raw D q budget positive fits event, failure]

theorem sumTo_fin (size : Nat) (event : Nat → Nat) :
    sumTo size event = ∑ index : Fin size, event index.val := by
  induction size with
  | zero => simp [sumTo]
  | succ size ih =>
    rw [sumTo, Fin.sum_univ_castSucc]
    simpa only [Fin.val_castSucc, Fin.val_last] using congrArg (fun n => n + event size) ih

theorem sumTo_field (event : ZMod Q → Nat) :
    sumTo (Q - 1) (fun i => event (model (i + 1))) =
      ∑ field : NonzeroField, event field.val := by
  rw [sumTo_fin]
  exact finFieldEquiv.sum_comp (fun field => event field.val)

theorem sumTo_field_pair (event : ZMod Q × ZMod Q → Nat) :
    sumTo (Q - 1) (fun i => sumTo (Q - 1) (fun j =>
      event (model (i + 1), model (j + 1)))) =
        ∑ pair : NonzeroField × NonzeroField, event (pair.1.val, pair.2.val) := by
  rw [sumTo_field (fun first => sumTo (Q - 1) (fun j => event (first, model (j + 1))))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  exact sumTo_field (fun second => event (first.val, second))

theorem field_event_count [Fact Q.Prime] {setup : IdealGroth16.Setup (ZMod Q)}
    (witness : IdealGroth16.WitnessOffsets setup) (event : IdealGroth16.Triple (ZMod Q) → Prop) :
    sumTo (Q - 1) (fun i => sumTo (Q - 1) (fun j =>
      if event (IdealGroth16.output witness (model (i + 1), model (j + 1))) then 1 else 0)) =
        IdealGroth16.nonzeroEventCount witness event := by
  classical
  rw [sumTo_field_pair (fun pair => if event (IdealGroth16.output witness pair) then 1 else 0)]
  rw [← IdealGroth16.nonzero_pair_event_count witness event]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

noncomputable def fieldObservationEvent {Ω : Type} [Fact Q.Prime]
    {setup : IdealGroth16.Setup (ZMod Q)} (witness : IdealGroth16.WitnessOffsets setup)
    (observe : IdealGroth16.Triple (ZMod Q) → Ω) (event : Ω → Prop) (failure : Ω) :
    Option (Nat × Nat) → Nat
  | none => if event failure then 1 else 0
  | some (r, s) => if event (observe (IdealGroth16.output witness (model r, model s))) then 1 else 0

/-- Exact arbitrary-event pushforward of the canonical sequential sampler.
The proof first partitions its actual successful Nat labels, then transports
that entire event through the field bijection. Failure mass is retained. -/
theorem pair_event_pushforward [Fact Q.Prime] {Ω : Type}
    {setup : IdealGroth16.Setup (ZMod Q)} (witness : IdealGroth16.WitnessOffsets setup)
    (observe : IdealGroth16.Triple (ZMod Q) → Ω) (event : Ω → Prop) (failure : Ω)
    (D budget : Nat) (fits : Q ≤ D) :
    pairMass D Q budget (fieldObservationEvent witness observe event failure) =
      IdealGroth16.boundedEventCount witness observe event failure (retryCount D Q) budget := by
  rw [pair_event_formula D Q budget (by decide) fits]
  simp only [fieldObservationEvent]
  have transported := field_event_count witness (event ∘ observe)
  simp only [Function.comp_def] at transported
  have exactTransport :
      (sumTo (Q - 1) (fun i => sumTo (Q - 1) (fun j =>
        if event (observe (IdealGroth16.output witness (model (i + 1), model (j + 1)))) then 1 else 0))) =
        IdealGroth16.nonzeroEventCount witness (event ∘ observe) := transported
  change pairMass D Q budget failureEvent * (if event failure then 1 else 0) +
    successWeight D Q budget ^ 2 * _ = _
  rw [exactTransport]
  rw [← IdealGroth16.SharedSampler.failure_count_matches D Q budget (by decide) fits,
    ← IdealGroth16.SharedSampler.weight_matches D Q budget fits]
  simp only [IdealGroth16.boundedEventCount, ZMod.card]
  by_cases acceptedFailure : event failure <;> simp [acceptedFailure]

/-- Every entropy coordinate now enumerates actual UInt8 byte tuples and
calls the runtime big-endian decoder before the same canonical pair loop. -/
theorem byte_pair_event_pushforward [Fact Q.Prime] {Ω : Type}
    {setup : IdealGroth16.Setup (ZMod Q)} (witness : IdealGroth16.WitnessOffsets setup)
    (observe : IdealGroth16.Triple (ZMod Q) → Ω) (event : Ω → Prop) (failure : Ω)
    (budget : Nat) :
    LeanCrypto.Probability.ByteEntropy.byteCount 32 (budget + budget) (pairSampler Q budget)
        (fieldObservationEvent witness observe event failure) =
      IdealGroth16.boundedEventCount witness observe event failure
        (retryCount (2 ^ 256) Q) budget := by
  rw [LeanCrypto.Probability.ByteEntropy.byteCount_eq_count,
    LeanCrypto.Probability.ByteEntropy.uint256_radix]
  exact pair_event_pushforward witness observe event failure (2 ^ 256) budget (by decide)

noncomputable def fieldObservedProbability {Ω : Type} [Fact Q.Prime]
    {setup : IdealGroth16.Setup (ZMod Q)} (witness : IdealGroth16.WitnessOffsets setup)
    (observe : IdealGroth16.Triple (ZMod Q) → Ω) (event : Ω → Prop) (failure : Ω)
    (D budget : Nat) : ℚ :=
  (pairMass D Q budget (fieldObservationEvent witness observe event failure) : ℚ) /
    D ^ (budget + budget)

theorem field_probability_pushforward [Fact Q.Prime] {Ω : Type}
    {setup : IdealGroth16.Setup (ZMod Q)} (witness : IdealGroth16.WitnessOffsets setup)
    (observe : IdealGroth16.Triple (ZMod Q) → Ω) (event : Ω → Prop) (failure : Ω)
    (D budget : Nat) (fits : Q ≤ D) :
    fieldObservedProbability witness observe event failure D budget =
      IdealGroth16.boundedEventProbability witness observe event failure (retryCount D Q) budget := by
  unfold fieldObservedProbability
  rw [pair_event_pushforward witness observe event failure D budget fits]
  unfold IdealGroth16.boundedEventProbability
  simp only [ZMod.card, IdealGroth16.SharedSampler.total_matches D Q budget fits, Nat.cast_pow]

/-- The ideal event-distance bound now applies to the proved field-cast
observation of the actual shared pure sampler, not only to matched weights.
The two observations must use the same setup, deterministic observer and
failure value. No worker, coordinate, QAP or release claim follows. -/
theorem field_observation_bound [Fact Q.Prime] {Ω : Type}
    {setup : IdealGroth16.Setup (ZMod Q)} (first second : IdealGroth16.WitnessOffsets setup)
    (observe : IdealGroth16.Triple (ZMod Q) → Ω) (event : Ω → Prop) (failure : Ω)
    (D budget : Nat) (fits : Q ≤ D) :
    |fieldObservedProbability first observe event failure D budget -
      fieldObservedProbability second observe event failure D budget| ≤
        (4 * (Q : ℚ)) / ((Q : ℚ) - 1) ^ 2 := by
  rw [field_probability_pushforward first observe event failure D budget fits,
    field_probability_pushforward second observe event failure D budget fits]
  simpa only [ZMod.card] using IdealGroth16.bounded_observation_bound first second
    observe event failure (retryCount D Q) budget

end LeanCrypto.Proofs.SamplerField

#print axioms LeanCrypto.Proofs.SamplerField.scalar_ext
#print axioms LeanCrypto.Proofs.SamplerField.scalar_model_nonzero
#print axioms LeanCrypto.Proofs.SamplerField.scalar_field_value
#print axioms LeanCrypto.Proofs.SamplerField.field_scalar_value
#print axioms LeanCrypto.Proofs.SamplerField.fin_field_value
#print axioms LeanCrypto.Proofs.SamplerField.admitValue_field
#print axioms LeanCrypto.Proofs.SamplerField.admitCandidate_field
#print axioms LeanCrypto.Proofs.SamplerField.candidate_field_sum
#print axioms LeanCrypto.Proofs.SamplerField.mass_event_formula
#print axioms LeanCrypto.Proofs.SamplerField.pair_event_formula_raw
#print axioms LeanCrypto.Proofs.SamplerField.pair_event_formula
#print axioms LeanCrypto.Proofs.SamplerField.sumTo_fin
#print axioms LeanCrypto.Proofs.SamplerField.sumTo_field
#print axioms LeanCrypto.Proofs.SamplerField.sumTo_field_pair
#print axioms LeanCrypto.Proofs.SamplerField.field_event_count
#print axioms LeanCrypto.Proofs.SamplerField.pair_event_pushforward
#print axioms LeanCrypto.Proofs.SamplerField.byte_pair_event_pushforward
#print axioms LeanCrypto.Proofs.SamplerField.field_probability_pushforward
#print axioms LeanCrypto.Proofs.SamplerField.field_observation_bound
