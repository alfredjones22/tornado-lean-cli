import TornadoProofs.ProofObservation
import LeanCryptoProofs.SamplerSupport

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TornadoProofs.ProofPrivacy

open LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Proofs.Groth16Assembly
open LeanCrypto.Probability.Rejection LeanCrypto.Sampling
open TornadoProofs.ProofObservation
attribute [local instance] Classical.propDecidable
local instance : Fact G1.scalarPrime.Prime := ⟨LeanCrypto.Proofs.Primes.bn254_scalar_prime⟩
local instance : NeZero G1.scalarPrime := ⟨by decide⟩

/-- Source-independent admission and honest setup relation for one fixed
witness/H input. `fromH` below derives its QAP obligation from the actual
FFT implementation and independent row equations. -/
structure Context where
  key : Types.QueryKey
  values : QueryScalars
  witness : Array Nat
  h : Array Nat
  setup : IdealGroth16.Setup Fr
  a : Polynomial Fr
  b : Polynomial Fr
  c : Polynomial Fr
  tau : Fr
  domain : Nat
  valid : ValidKey key
  dimensions : Dimensions key witness h
  witnessCanonical : witness.all (· < MSM.order) = true
  hCanonical : h.all (· < MSM.order) = true
  span : KeySpan key values
  relation : QapRelation key values witness h setup a b c tau domain
  quotient : a.eval tau * b.eval tau - c.eval tau =
    (LeanCrypto.Proofs.FFT.coeffPolynomial h).eval tau * (tau ^ domain - 1)

noncomputable def Context.offsets (context : Context) : IdealGroth16.WitnessOffsets context.setup :=
  qapOffsets context.key context.values context.witness context.h context.setup context.a context.b
    context.c context.tau context.domain context.relation context.quotient

def Context.signals (context : Context) : Array Nat :=
  context.witness.extract 1 (context.key.nPublic + 1)

def Context.observe (context : Context) (triple : IdealGroth16.Triple Fr) :
    Option (ByteArray × Array Nat) :=
  pointObservation (canonicalPoints context.signals triple) context.signals

/-- Actual native assemble followed by the exact original acceptance observer.
A sampler failure and every assembly/normalization/verifier failure are visible
as `none`, matching the worker's fixed failure channel. -/
def Context.native (context : Context) : Option (Nat × Nat) → Option (ByteArray × Array Nat)
  | none => none
  | some (r, s) =>
    match MSM.assemble context.key context.witness context.h r s with
    | .error _ => none
    | .ok points => pointObservation points context.signals

theorem native_eq_observe (context : Context) (r s : Nat)
    (rBound : r < G1.scalarPrime) (sBound : s < G1.scalarPrime) :
    context.native (some (r, s)) =
      context.observe (IdealGroth16.output context.offsets ((r : Fr), (s : Fr))) := by
  let canonical : Canonical context.witness context.h r s :=
    ⟨rBound, sBound, context.witnessCanonical, context.hCanonical⟩
  have constructed := assemble_construct context.key context.witness context.h r s
    context.valid context.dimensions canonical
  have admitted := construction_admitted context.key context.witness context.h r s context.valid
  have meaning := construction_scalarOutput context.key context.values context.witness context.h r s
    context.valid context.dimensions canonical context.span
  unfold Context.native
  dsimp only
  rw [constructed]
  dsimp only
  have factor := point_observation_factors (construction context.key context.witness context.h r s)
    (scalarOutput context.key context.values context.witness context.h r s) context.signals
    rfl admitted.1 admitted.2.1 admitted.2.2 meaning.1 meaning.2.1 meaning.2.2
  rw [factor]
  unfold Context.observe Context.offsets
  rw [scalarOutput_eq_ideal context.key context.values context.witness context.h context.setup
    context.a context.b context.c context.tau context.domain context.relation context.quotient r s]

noncomputable def Context.event (context : Context)
    (event : Option (ByteArray × Array Nat) → Prop) : Option (Nat × Nat) → Nat :=
  fun masks => if event (context.native masks) then 1 else 0

/-- Exact unconditioned event mass of actual native proof construction and
all acceptance failures equals the proved ideal field observation mass. -/
theorem actual_event_mass (context : Context) (event : Option (ByteArray × Array Nat) → Prop)
    (D budget : Nat) (fits : G1.scalarPrime ≤ D) :
    pairMass D G1.scalarPrime budget (context.event event) =
      pairMass D G1.scalarPrime budget
        (LeanCrypto.Proofs.SamplerField.fieldObservationEvent context.offsets context.observe event none) := by
  classical
  apply LeanCrypto.Proofs.SamplerField.pairMass_congr_admissible D G1.scalarPrime budget
    (by decide) fits
  · rfl
  · intro r s _ rBound _ sBound
    unfold Context.event LeanCrypto.Proofs.SamplerField.fieldObservationEvent
    rw [native_eq_observe context r s rBound sBound]
    rfl

noncomputable def Context.probability (context : Context)
    (event : Option (ByteArray × Array Nat) → Prop) (D budget : Nat) : ℚ :=
  (pairMass D G1.scalarPrime budget (context.event event) : ℚ) / D ^ (budget + budget)

theorem actual_probability_eq_field (context : Context)
    (event : Option (ByteArray × Array Nat) → Prop) (D budget : Nat)
    (fits : G1.scalarPrime ≤ D) :
    context.probability event D budget =
      LeanCrypto.Proofs.SamplerField.fieldObservedProbability context.offsets
        context.observe event none D budget := by
  unfold Context.probability LeanCrypto.Proofs.SamplerField.fieldObservedProbability
  rw [actual_event_mass context event D budget fits]
  rfl

/-- Statistical witness privacy of the exact native proof payload plus
failure verdict, conditional on honest setup/query and QAP source admission.
Both contexts must have the SAME public setup and public signals. This says
nothing about time, memory, history queries, OS entropy, or malicious setup. -/
theorem actual_observation_bound (first second : Context)
    (sameSetup : first.setup = second.setup) (sameSignals : first.signals = second.signals)
    (event : Option (ByteArray × Array Nat) → Prop) (D budget : Nat)
    (fits : G1.scalarPrime ≤ D) :
    |first.probability event D budget - second.probability event D budget| ≤
      (4 * (G1.scalarPrime : ℚ)) / ((G1.scalarPrime : ℚ) - 1) ^ 2 := by
  rw [actual_probability_eq_field first event D budget fits,
    actual_probability_eq_field second event D budget fits]
  have observers : first.observe = second.observe := by
    funext triple
    unfold Context.observe
    rw [sameSignals]
  rw [observers]
  cases first with
  | mk key values witness h setup a b c tau domain valid dimensions wc hc span relation quotient =>
    cases second with
    | mk key2 values2 witness2 h2 setup2 a2 b2 c2 tau2 domain2 valid2 dimensions2 wc2 hc2 span2 relation2 quotient2 =>
      dsimp only at sameSetup
      cases sameSetup
      exact LeanCrypto.Proofs.SamplerField.field_observation_bound _ _ _ _ _ D budget fits

/-- Closed numerical interpretation of the explicit BN254 event bound. -/
theorem bn254_event_bound_bits :
    (4 * (G1.scalarPrime : ℚ)) / ((G1.scalarPrime : ℚ) - 1) ^ 2 ≤ (1 : ℚ) / 2 ^ 251 := by
  norm_num [G1.scalarPrime, LeanCrypto.BN254.Constants.scalarPrime, LeanCrypto.bn254ScalarPrime]

theorem actual_observation_bound_bits (first second : Context)
    (sameSetup : first.setup = second.setup) (sameSignals : first.signals = second.signals)
    (event : Option (ByteArray × Array Nat) → Prop) (D budget : Nat)
    (fits : G1.scalarPrime ≤ D) :
    |first.probability event D budget - second.probability event D budget| ≤ (1 : ℚ) / 2 ^ 251 :=
  (actual_observation_bound first second sameSetup sameSignals event D budget fits).trans bn254_event_bound_bits

end TornadoProofs.ProofPrivacy

#print axioms TornadoProofs.ProofPrivacy.native_eq_observe
#print axioms TornadoProofs.ProofPrivacy.actual_event_mass
#print axioms TornadoProofs.ProofPrivacy.actual_probability_eq_field
#print axioms TornadoProofs.ProofPrivacy.actual_observation_bound

#print axioms TornadoProofs.ProofPrivacy.bn254_event_bound_bits
#print axioms TornadoProofs.ProofPrivacy.actual_observation_bound_bits
