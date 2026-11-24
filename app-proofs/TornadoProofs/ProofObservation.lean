import Tornado.Protocol.ClassicProofPipeline
import LeanCryptoProofs.AssemblyQap

open Lean Elab Term Meta
elab "actualAcceptPoints" : term =>
  mkConstWithFreshMVarLevels
    (mkPrivateNameCore `Tornado.Protocol.ClassicProofPipeline
      `Tornado.Protocol.ClassicProofPipeline.acceptPoints)

elab "unfoldOriginalAccept" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic1 fun goal => goal.deltaTarget (· ==
    mkPrivateNameCore `Tornado.Protocol.ClassicProofPipeline
      `Tornado.Protocol.ClassicProofPipeline.acceptPoints)

set_option autoImplicit false

namespace TornadoProofs.ProofObservation

open Tornado.Protocol
open LeanCrypto.Proofs.Groth16Assembly

abbrev originalAcceptPoints := actualAcceptPoints

/-- Public payload and failure observation of the original acceptPoints.
The erased checked-witness certificate is not part of this observation. -/
def originalObservation (circuit : WitnessVM.PinnedCircuit)
    (checked : Groth16MSM.CheckedProofPoints circuit) (signals : Array Nat) :
    Option (ByteArray × Array Nat) :=
  ((originalAcceptPoints circuit checked signals).toOption).map
    (fun accepted => (accepted.artifact.bytes, accepted.artifact.expectedSignals))

/-- Full native proof check as a pure deterministic observer, including
original signal equality, normalizers, on-curve guards, byte encoding and
compiled-key verifier. All errors remain the same observed failure. -/
def pointObservation (points : Groth16MSM.ProofPoints) (signals : Array Nat) :
    Option (ByteArray × Array Nat) :=
  if points.publicSignals = signals then
    match ClassicProofPipeline.toVerifierProof points with
    | .error _ => none
    | .ok proof =>
      match Groth16MSM.solidityProofBytes points with
      | .error _ => none
      | .ok bytes =>
        match ClassicVerifyingKey.verifyClassic proof signals with
        | .ok true => some (bytes, signals)
        | _ => none
  else none

theorem original_observation_eq_points (circuit : WitnessVM.PinnedCircuit)
    (checked : Groth16MSM.CheckedProofPoints circuit) (signals : Array Nat) :
    originalObservation circuit checked signals = pointObservation checked.points signals := by
  unfold originalObservation originalAcceptPoints pointObservation
  unfoldOriginalAccept
  split
  · split
    · simp_all [Except.toOption, Option.map]
    · split
      · simp_all [Except.toOption, Option.map]
      · split <;> simp_all [Except.toOption, Option.map]
  · simp_all [Except.toOption, Option.map]

theorem verifierProof_factors (points : Groth16MSM.ProofPoints)
    (triple : IdealGroth16.Triple Fr) (signals : Array Nat)
    (a : G1Admitted points.piA) (b : G2Admitted points.piB) (c : G1Admitted points.piC)
    (aMeaning : g1 points.piA = scalarG1 triple.a)
    (bMeaning : g2 points.piB = scalarG2 triple.b)
    (cMeaning : g1 points.piC = scalarG1 triple.c) :
    ClassicProofPipeline.toVerifierProof points =
      ClassicProofPipeline.toVerifierProof (canonicalPoints signals triple) := by
  obtain ⟨ha, hb, hc⟩ := normalization_factors_through_triple points triple signals
    a b c aMeaning bMeaning cMeaning
  unfold ClassicProofPipeline.toVerifierProof
  rw [ha, hb, hc]

/-- Native acceptance/rejection and exact released proof payload factor
through the ideal triple. No pairing correctness or acceptance assumption
is needed: the same deterministic verifier verdict is retained on both sides. -/
theorem point_observation_factors (points : Groth16MSM.ProofPoints)
    (triple : IdealGroth16.Triple Fr) (signals : Array Nat)
    (signalsEqual : points.publicSignals = signals)
    (a : G1Admitted points.piA) (b : G2Admitted points.piB) (c : G1Admitted points.piC)
    (aMeaning : g1 points.piA = scalarG1 triple.a)
    (bMeaning : g2 points.piB = scalarG2 triple.b)
    (cMeaning : g1 points.piC = scalarG1 triple.c) :
    pointObservation points signals = pointObservation (canonicalPoints signals triple) signals := by
  have verifier := verifierProof_factors points triple signals a b c aMeaning bMeaning cMeaning
  have encoded := serialization_factors_through_triple points triple signals a b c aMeaning bMeaning cMeaning
  unfold pointObservation
  rw [signalsEqual, if_pos rfl]
  change _ = if signals = signals then _ else _
  rw [if_pos rfl, verifier, encoded]

end TornadoProofs.ProofObservation

#print axioms TornadoProofs.ProofObservation.original_observation_eq_points
#print axioms TornadoProofs.ProofObservation.verifierProof_factors
#print axioms TornadoProofs.ProofObservation.point_observation_factors
