import Lean
import Tornado.Compression.Gzip
import Tornado.Protocol.Groth16MSM
import Tornado.Protocol.ClassicVerifyingKey

/-!
Composition of the native Classic withdrawal prover and verifier, used by
the isolated CLI prover worker. Circuit/key bytes are authenticated before
use. Arithmetic is variable-time and does not guarantee secret erasure.
The caller supplies blinding scalars; this module does not sample entropy.
-/

namespace Tornado.Protocol.ClassicProofPipeline

open Lean Tornado.Protocol

structure PinnedAssets where
  graph : WitnessVM.PinnedGraph
  circuit : WitnessVM.PinnedCircuit
  key : ProvingKey.PinnedKey

structure ReviewedPublic where
  root : Nat
  nullifierHash : Nat
  recipient : Nat
  relayer : Nat
  fee : Nat
  refund : Nat

def ReviewedPublic.ofWithdrawal (withdrawal : TornadoWitness.WithdrawalInput) :
    ReviewedPublic :=
  ⟨withdrawal.expectedRoot, withdrawal.note.nullifierHash,
    withdrawal.recipient, withdrawal.relayer, withdrawal.fee, withdrawal.refund⟩

def ReviewedPublic.signals (reviewed : ReviewedPublic) : Array Nat :=
  #[reviewed.root, reviewed.nullifierHash, reviewed.recipient,
    reviewed.relayer, reviewed.fee, reviewed.refund]

/-- Authenticate the exact bundled compressed circuit/key, the complete
    extracted witness graph, and the decoded R1CS before proving. -/
def loadBundled (compressedCircuit compressedKey : ByteArray)
    (graphText : String) : Except String PinnedAssets := do
  let pinnedGraph ← WitnessVM.decodePinnedGraph graphText
  let circuitBytes ← Tornado.Compression.Gzip.pinnedCircuit compressedCircuit
  let some circuitText := String.fromUTF8? circuitBytes
    | throw "Pinned Tornado circuit is not UTF-8."
  let circuitJson ← Json.parse circuitText
  let circuit ← Groth16R1CS.decodeCircuit circuitJson
  let pinnedCircuit ← WitnessVM.authenticatePinnedCircuit circuit
  let keyBytes ← Tornado.Compression.Gzip.pinnedProvingKey compressedKey
  let pinnedKey ← ProvingKey.authenticatePinnedKey keyBytes
  return { graph := pinnedGraph, circuit := pinnedCircuit, key := pinnedKey }

/-- Convert the same three proof points that will be serialized to the
    checked public verifier representation. Infinity fails closed. -/
def toVerifierProof (points : Groth16MSM.ProofPoints) :
    Except String BN254Groth16Verify.Proof := do
  let some a ← points.piA.toAffine
    | throw "Classic proof A is infinity."
  let some b ← points.piB.toAffine
    | throw "Classic proof B is infinity."
  let some c ← points.piC.toAffine
    | throw "Classic proof C is infinity."
  if !a.onCurve || !b.onCurve || !c.onCurve then
    throw "Classic proof contains an off-curve point."
  return { a, b, c }

/-- An accepted artifact carries kernel-visible evidence that the exact
    returned points passed the native R1CS gate, serialization and Classic
    verification. The mathematical correctness of those computations is not
    established by these fields. -/
structure CheckedArtifact (circuit : WitnessVM.PinnedCircuit) where
  private mk ::
  checkedPoints : Groth16MSM.CheckedProofPoints circuit
  bytes : ByteArray
  proof : BN254Groth16Verify.Proof
  expectedSignals : Array Nat
  signalsEqual : checkedPoints.points.publicSignals = expectedSignals
  proofMatchesPoints : toVerifierProof checkedPoints.points = .ok proof
  serialization : Groth16MSM.solidityProofBytes checkedPoints.points = .ok bytes
  verification : ClassicVerifyingKey.verifyClassic proof expectedSignals = .ok true

structure AcceptedPoints (circuit : WitnessVM.PinnedCircuit)
    (expectedSignals : Array Nat) where
  private mk ::
  artifact : CheckedArtifact circuit
  binding : artifact.expectedSignals = expectedSignals

/-- Check public-signal binding, byte serialization and the immutable-key
    Classic pairing equation before exposing a proof artifact. -/
private def acceptPoints (circuit : WitnessVM.PinnedCircuit)
    (checked : Groth16MSM.CheckedProofPoints circuit)
    (expectedSignals : Array Nat) : Except String (AcceptedPoints circuit expectedSignals) :=
  if hsignals : checked.points.publicSignals = expectedSignals then
    match hproof : toVerifierProof checked.points with
    | .error message => .error message
    | .ok proof =>
      match hbytes : Groth16MSM.solidityProofBytes checked.points with
      | .error message => .error message
      | .ok bytes =>
        match hverified : ClassicVerifyingKey.verifyClassic proof expectedSignals with
        | .error message => .error message
        | .ok false => .error "Classic proof equation rejected the native points."
        | .ok true => .ok ⟨⟨checked, bytes, proof, expectedSignals,
            hsignals, hproof, hbytes, hverified⟩, rfl⟩
  else .error "Native proof public signals differ from the reviewed withdrawal."

/-- Public output only. The checked witness and withdrawal input occur in a
    proposition, which is erased from the compiled result. -/
structure PublicProof (circuit : WitnessVM.PinnedCircuit) where
  private mk ::
  bytes : ByteArray
  signals : Array Nat
  reviewed : ReviewedPublic
  certificate : ∃ artifact : CheckedArtifact circuit,
    artifact.bytes = bytes ∧
    artifact.expectedSignals = signals ∧
    artifact.expectedSignals = reviewed.signals

/-- Complete native public-reference proving route. Caller supplied `r,s`
    are required to be nonzero canonical Fr elements. They are deliberately
    explicit, so callers cannot mistake a deterministic fixture for securely
    randomized production blinding. -/
def prove (assets : PinnedAssets) (withdrawal : TornadoWitness.WithdrawalInput)
    (r s : Nat) : Except String (PublicProof assets.circuit) := do
  if r == 0 || s == 0 || r >= BN254G1.scalarPrime ||
      s >= BN254G1.scalarPrime then
    throw "Classic proof blinding scalars must be nonzero canonical Fr values."
  let inputs ← TornadoWitness.prepareInputPrefix withdrawal
  let reviewed := ReviewedPublic.ofWithdrawal withdrawal
  let expectedSignals := reviewed.signals
  if inputs.extract 1 7 != expectedSignals then
    throw "Withdrawal public input prefix differs from reviewed values."
  let checked ← Groth16MSM.deriveCheckedProofPoints assets.key assets.graph
    assets.circuit inputs withdrawal.note.commitment r s
  let accepted ← acceptPoints assets.circuit checked expectedSignals
  let artifact := accepted.artifact
  return ⟨artifact.bytes, artifact.expectedSignals, reviewed,
    ⟨artifact, rfl, rfl, accepted.binding⟩⟩

/-- A returned artifact has passed the exact native full R1CS gate. -/
theorem checked_artifact_has_full_witness (circuit : WitnessVM.PinnedCircuit)
    (artifact : CheckedArtifact circuit) :
    Groth16R1CS.checkCircuit circuit.circuit artifact.checkedPoints.witness =
      .ok 28275 :=
  Groth16MSM.derived_points_use_checked_witness circuit artifact.checkedPoints

/-- The returned bytes are the checked points' Solidity encoding. -/
theorem checked_artifact_serializes_points (circuit : WitnessVM.PinnedCircuit)
    (artifact : CheckedArtifact circuit) :
    Groth16MSM.solidityProofBytes artifact.checkedPoints.points = .ok artifact.bytes :=
  artifact.serialization

/-- The returned proof passed the compiled-in Classic key and uses exactly
    the expected public signal array. -/
theorem checked_artifact_verifies_expected_signals
    (circuit : WitnessVM.PinnedCircuit) (artifact : CheckedArtifact circuit) :
    ClassicVerifyingKey.verifyClassic artifact.proof artifact.expectedSignals =
      .ok true ∧ artifact.checkedPoints.points.publicSignals = artifact.expectedSignals :=
  ⟨artifact.verification, artifact.signalsEqual⟩

/-- Any accepted artifact's public inputs are canonical BN254 Fr values. -/
theorem checked_artifact_signals_bounded
    (circuit : WitnessVM.PinnedCircuit) (artifact : CheckedArtifact circuit) :
    artifact.expectedSignals.all (· < BN254G1.scalarPrime) = true :=
  ClassicVerifyingKey.verifyClassic_true_signals_bounded
    artifact.proof artifact.expectedSignals artifact.verification

/-- The public array is exactly the six values displayed for review. -/
theorem public_proof_binds_review (circuit : WitnessVM.PinnedCircuit)
    (result : PublicProof circuit) : result.signals = result.reviewed.signals := by
  obtain ⟨artifact, _, hsignals, hreview⟩ := result.certificate
  exact hsignals.symm.trans hreview

/-- The returned bytes are an encoding of points assembled from a witness
    that passed the complete executable R1CS check. -/
theorem public_proof_checked_and_encoded (circuit : WitnessVM.PinnedCircuit)
    (result : PublicProof circuit) :
    ∃ artifact : CheckedArtifact circuit,
      Groth16R1CS.checkCircuit circuit.circuit artifact.checkedPoints.witness =
        .ok 28275 ∧
      Groth16MSM.solidityProofBytes artifact.checkedPoints.points = .ok result.bytes := by
  obtain ⟨artifact, hbytes, _, _⟩ := result.certificate
  exact ⟨artifact, checked_artifact_has_full_witness circuit artifact,
    artifact.serialization.trans (congrArg Except.ok hbytes)⟩

/-- The exact returned public array passed the compiled-key verifier. -/
theorem public_proof_verified (circuit : WitnessVM.PinnedCircuit)
    (result : PublicProof circuit) :
    ∃ proof : BN254Groth16Verify.Proof,
      ClassicVerifyingKey.verifyClassic proof result.signals = .ok true := by
  obtain ⟨artifact, _, hsignals, _⟩ := result.certificate
  exact ⟨artifact.proof, by simpa [← hsignals] using artifact.verification⟩

/-- The accepted public values are canonical Fr elements. -/
theorem public_proof_signals_bounded (circuit : WitnessVM.PinnedCircuit)
    (result : PublicProof circuit) :
    result.signals.all (· < BN254G1.scalarPrime) = true := by
  obtain ⟨artifact, _, hsignals, _⟩ := result.certificate
  simpa [← hsignals] using checked_artifact_signals_bounded circuit artifact

end Tornado.Protocol.ClassicProofPipeline

#print axioms Tornado.Protocol.ClassicProofPipeline.checked_artifact_has_full_witness
#print axioms Tornado.Protocol.ClassicProofPipeline.checked_artifact_serializes_points
#print axioms Tornado.Protocol.ClassicProofPipeline.checked_artifact_verifies_expected_signals
#print axioms Tornado.Protocol.ClassicProofPipeline.checked_artifact_signals_bounded
#print axioms Tornado.Protocol.ClassicProofPipeline.public_proof_binds_review
#print axioms Tornado.Protocol.ClassicProofPipeline.public_proof_checked_and_encoded
#print axioms Tornado.Protocol.ClassicProofPipeline.public_proof_verified
#print axioms Tornado.Protocol.ClassicProofPipeline.public_proof_signals_bounded
