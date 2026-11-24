import LeanCryptoProofs.Groth16IdealPrivacy
import LeanCrypto.Probability.Pair

/-!
Count-only bridge to the actual shared pure `samplePairLoop` interpreter.
This does not identify its natural-number labels with the algebraic field,
and does not connect ideal triples to curve coordinates, MSM, QAP, the
proving key, pairing or serialization. No application ZK claim follows.
-/

namespace IdealGroth16.SharedSampler

attribute [local instance] Classical.propDecidable

open LeanCrypto.Probability.Rejection LeanCrypto.Sampling

/-- The explicit ideal finite-tape weight agrees with the weight derived
from the shared pure bounded-retry loop. -/
theorem weight_matches (D q budget : Nat) (fits : q ≤ D) :
    perValueWeight (q - 1) (retryCount D q) budget = successWeight D q budget := by
  have partition : q - 1 + retryCount D q = D := by unfold retryCount; omega
  induction budget with
  | zero => rfl
  | succ n ih => simp only [perValueWeight, successWeight, partition, ih]

theorem total_matches (D q budget : Nat) (fits : q ≤ D) :
    retryPairTotal (q - 1) (retryCount D q) budget = D ^ (budget + budget) := by
  have partition : q - 1 + retryCount D q = D := by unfold retryCount; omega
  simp only [retryPairTotal, partition, pow_two, pow_add]

/-- Success multiplicity of each admissible returned pair, obtained from
the shared sequential sampler's actual count theorem. -/
theorem value_count_matches (D q budget r s : Nat) (positive : 0 < q) (fits : q ≤ D)
    (allowedR : admissible q r = true) (allowedS : admissible q s = true) :
    pairMass D q budget (pairValueEvent r s) =
      (perValueWeight (q - 1) (retryCount D q) budget) ^ 2 := by
  rw [pair_joint_factorizes, scalar_count D q budget r positive fits,
    scalar_count D q budget s positive fits, if_pos allowedR, if_pos allowedS,
    weight_matches D q budget fits, pow_two]

/-- The whole successful mass agrees, without conditioning on success. -/
theorem success_count_matches (D q budget : Nat) (positive : 0 < q) (fits : q ≤ D) :
    retryPairSuccess (q - 1) (retryCount D q) budget = pairMass D q budget successEvent := by
  rw [pair_success_count, success_count D q budget positive fits]
  simp only [retryPairSuccess, weight_matches D q budget fits, mul_pow]

/-- All failures of either scalar retry loop agree in the two models. -/
theorem failure_count_matches (D q budget : Nat) (positive : 0 < q) (fits : q ≤ D) :
    retryPairFailure (q - 1) (retryCount D q) budget = pairMass D q budget failureEvent := by
  have actual := pair_normalization D q budget
  have ideal := retry_pair_normalization (q - 1) (retryCount D q) budget
  rw [total_matches D q budget fits, success_count_matches D q budget positive fits] at ideal
  omega

/-- The success coefficient in the unconditioned mixture is exactly the
probability mass derived from the shared sequential interpreter. -/
theorem success_probability_matches (F : Type*) [Field F] [Fintype F]
    (D budget : Nat) (fits : Fintype.card F ≤ D) :
    retrySuccessProbability F (retryCount D (Fintype.card F)) budget =
      (pairMass D (Fintype.card F) budget successEvent : ℚ) / D ^ (budget + budget) := by
  have positive : 0 < Fintype.card F := Fintype.card_pos_iff.mpr inferInstance
  rw [retrySuccessProbability, success_count_matches D (Fintype.card F) budget positive fits,
    total_matches D (Fintype.card F) budget fits, Nat.cast_pow]

/-- The failure coefficient is preserved as an observed outcome; it is
not dropped by passing to a conditional successful-output distribution. -/
theorem failure_probability_matches (F : Type*) [Field F] [Fintype F]
    (D budget : Nat) (fits : Fintype.card F ≤ D) :
    retryFailureProbability F (retryCount D (Fintype.card F)) budget =
      (pairMass D (Fintype.card F) budget failureEvent : ℚ) / D ^ (budget + budget) := by
  have positive : 0 < Fintype.card F := Fintype.card_pos_iff.mpr inferInstance
  rw [retryFailureProbability, failure_count_matches D (Fintype.card F) budget positive fits,
    total_matches D (Fintype.card F) budget fits, Nat.cast_pow]

/-- An exact unconditioned ideal-triple mixture whose coefficients now use
the actual shared pure retry-loop counts. Its field-label representation
and curve/QAP implementation bridges remain separate obligations. -/
theorem ideal_mixture_with_shared_counts {F Ω : Type*} [Field F] [Fintype F]
    {p : Setup F} (w : WitnessOffsets p) (observe : Triple F → Ω) (event : Ω → Prop)
    (failure : Ω) (D budget : Nat) (fits : Fintype.card F ≤ D) :
    boundedEventProbability w observe event failure (retryCount D (Fintype.card F)) budget =
      ((pairMass D (Fintype.card F) budget failureEvent : ℚ) / D ^ (budget + budget)) *
        (if event failure then 1 else 0) +
      ((pairMass D (Fintype.card F) budget successEvent : ℚ) / D ^ (budget + budget)) *
        nonzeroEventProbability w (event ∘ observe) := by
  rw [bounded_probability_mixture, success_probability_matches F D budget fits,
    failure_probability_matches F D budget fits]

end IdealGroth16.SharedSampler

#print axioms IdealGroth16.SharedSampler.weight_matches
#print axioms IdealGroth16.SharedSampler.total_matches
#print axioms IdealGroth16.SharedSampler.value_count_matches
#print axioms IdealGroth16.SharedSampler.success_count_matches
#print axioms IdealGroth16.SharedSampler.failure_count_matches
#print axioms IdealGroth16.SharedSampler.success_probability_matches
#print axioms IdealGroth16.SharedSampler.failure_probability_matches
#print axioms IdealGroth16.SharedSampler.ideal_mixture_with_shared_counts
