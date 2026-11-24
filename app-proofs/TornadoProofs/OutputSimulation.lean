import TornadoProofs.WorkerPrefix

set_option autoImplicit false
namespace TornadoProofs.OutputSimulation
open LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Proofs.Groth16Assembly
open Tornado.Protocol Tornado.Runtime.WorkerProgram Tornado.Protocol.ProverWorkerWire
open TornadoProofs.ProofObservation TornadoProofs.ProofPrivacy TornadoProofs.WorkerOutput
open TornadoProofs.WorkerEntropy TornadoProofs.WorkerPrefix

local instance : Fact G1.scalarPrime.Prime := ⟨LeanCrypto.Proofs.Primes.bn254_scalar_prime⟩
local instance : NeZero G1.scalarPrime := ⟨by decide⟩

/-- Witness-free reference offsets. The abstract setup contains its scalar
trapdoor; this is not a public trapdoor-recovery algorithm or runnable signer. -/
noncomputable def referenceOffsets (setup : IdealGroth16.Setup Fr) : IdealGroth16.WitnessOffsets setup :=
  ⟨0,0,-setup.kappa/setup.delta,by
    field_simp [setup.delta_ne_zero]
    ring⟩

def referenceObservation (signals : Array Nat) (triple : IdealGroth16.Triple Fr) :
    Option (ByteArray × Array Nat) := pointObservation (canonicalPoints signals triple) signals

noncomputable def referenceProbability (setup : IdealGroth16.Setup Fr) (signals : Array Nat)
    (event : Option (ByteArray × Array Nat) → Prop) (D budget : Nat) : ℚ :=
  LeanCrypto.Proofs.SamplerField.fieldObservedProbability (referenceOffsets setup)
    (referenceObservation signals) event none D budget

/-- Comparison with a SINGLE explicitly defined witness-free reference,
not only with a second hypothetical valid witness of the same statement. -/
theorem native_reference_bound (context : Context)
    (event : Option (ByteArray × Array Nat) → Prop) (D budget : Nat) (fits : G1.scalarPrime ≤ D) :
    |context.probability event D budget - referenceProbability context.setup context.signals event D budget| ≤
      (4*(G1.scalarPrime : ℚ))/((G1.scalarPrime : ℚ)-1)^2 := by
  rw [actual_probability_eq_field context event D budget fits]
  exact LeanCrypto.Proofs.SamplerField.field_observation_bound context.offsets (referenceOffsets context.setup)
    context.observe event none D budget fits

theorem native_reference_bound_bits (context : Context)
    (event : Option (ByteArray × Array Nat) → Prop) (D budget : Nat) (fits : G1.scalarPrime ≤ D) :
    |context.probability event D budget - referenceProbability context.setup context.signals event D budget| ≤
      (1 : ℚ)/2^251 :=
  (native_reference_bound context event D budget fits).trans bn254_event_bound_bits

/-- This reference depends on public-to-parent request data, public signals
and the abstract setup, and contains no note, circuit witness, key-query
arrays, H coefficients or real witness offsets. Every failure is retained. -/
noncomputable def referenceTerminalProbability (setup : IdealGroth16.Setup Fr)
    (signals : Array Nat) (request : Request) (event : String × String × UInt32 → Prop) : ℚ :=
  referenceProbability setup signals
    (fun payload => event (terminalObservation request (requestObservation request payload)))
    (2^256) LeanCrypto.Sampling.maxAttempts

theorem original_worker_reference_bound (noteIndex : Option String) (request : Request)
    (replies : File → Option ByteArray) (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput)
    (admission : interpret replies (prefixProgram noteIndex request) = .done (assets,withdrawal))
    (context : Context) (source : TornadoProofs.PipelineComposition.ExecutionSource assets withdrawal context)
    (event : String × String × UInt32 → Prop) :
    |fullProbability replies noteIndex request event -
      referenceTerminalProbability context.setup context.signals request event| ≤ (1 : ℚ)/2^251 := by
  rw [fullProbability_after_admission noteIndex request replies assets withdrawal admission,
    probability_eq_context replies assets withdrawal context source request]
  exact native_reference_bound_bits context _ _ _ (by decide)

end TornadoProofs.OutputSimulation
#print axioms TornadoProofs.OutputSimulation.native_reference_bound
#print axioms TornadoProofs.OutputSimulation.native_reference_bound_bits
#print axioms TornadoProofs.OutputSimulation.original_worker_reference_bound
