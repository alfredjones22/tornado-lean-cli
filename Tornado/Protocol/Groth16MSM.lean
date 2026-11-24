import Lean
import Tornado.Protocol.BN254G1
import Tornado.Protocol.BN254G2
import Tornado.Protocol.ProvingKey
import Tornado.Protocol.FrFFT
import Tornado.Protocol.WitnessVM
import Tornado.Protocol.Abi

import LeanCrypto.Groth16.MSM

/-! Legacy aliases plus pinned Tornado artifact/witness adapters. The
reusable point arithmetic and generic assembly live in lean-crypto. -/

namespace Tornado.Protocol.Groth16MSM

open Tornado.Protocol

export LeanCrypto.Groth16.Types
  (QueryKey QueryKey.mk QueryKey.nPublic QueryKey.vkAlpha1 QueryKey.vkBeta1
   QueryKey.vkDelta1 QueryKey.vkBeta2 QueryKey.vkDelta2 QueryKey.queryA QueryKey.queryB1
   QueryKey.queryB2 QueryKey.queryC QueryKey.hExps
   ProofPoints ProofPoints.mk ProofPoints.piA ProofPoints.piB ProofPoints.piC ProofPoints.publicSignals)
export LeanCrypto.Groth16.MSM
  (order msmG1 msmG2 solidityProofBytes assemble
   msmG1_rejects_mismatched_counts msmG2_rejects_mismatched_counts)

def QueryKey.fromParsed (key : ProvingKey.ParsedKey) : QueryKey :=
  ⟨key.header.nPublic, key.vkAlpha1, key.vkBeta1, key.vkDelta1,
    key.vkBeta2, key.vkDelta2, key.queryA, key.queryB1, key.queryB2,
    key.queryC, key.hExps⟩

/-- The pinned binary parser already authenticates the complete key, but
    `ParsedKey` itself is a public structure. This adapter checks its pinned
    dimensions again; it does not establish provenance unless the caller
    obtains the value from `decodeFullKey`. -/
def assembleParsed (key : ProvingKey.ParsedKey) (witness h : Array Nat)
    (r s : Nat) : Except String ProofPoints := do
  if key.header.nVars != 28300 || key.header.nPublic != 6 ||
      key.header.domainSize != 32768 || key.hExps.size != 32767 then
    throw "Groth16 parsed key does not have the pinned Tornado dimensions."
  assemble (QueryKey.fromParsed key) witness h r s

/-- Exact native derivation provenance. Secret-bearing intermediate values
occur only under this erased proposition; this is not a QAP correctness law. -/
def Derivation (key : ProvingKey.PinnedKey) (graph : WitnessVM.PinnedGraph)
    (circuit : WitnessVM.PinnedCircuit) (inputs : Array Nat) (commitment r s : Nat)
    (witness : Array Nat) (points : ProofPoints) : Prop :=
  ∃ decoded h,
    WitnessVM.generateCheckedWitness graph circuit inputs commitment = .ok witness ∧
    ProvingKey.decodeFullKey key = .ok decoded ∧
    FrFFT.calculateH decoded.header.domainSize witness decoded.polsA decoded.polsB = .ok h ∧
    assembleParsed decoded witness h r s = .ok points

/-- The private constructor records the exact native R1CS check and an
    actual H/assembly derivation for these points. It does not certify the
    mathematical elliptic-curve protocol equation or recipient/chain state. -/
structure CheckedProofPoints (circuit : WitnessVM.PinnedCircuit) where
  private mk ::
  witness : Array Nat
  points : ProofPoints
  checked : Groth16R1CS.checkCircuit circuit.circuit witness = .ok 28275
  constructed : ∃ key graph inputs commitment r s,
    Derivation key graph circuit inputs commitment r s witness points

/-- Pure, authenticated-artifact route from the pinned Circom input to proof
    points. Blinding scalars are explicit to keep randomness outside this
    function. Its full 28,300-signal output matches a pinned SDK oracle for
    one public fixture, but the formula is not formally proven correct and
    this route must not process funded-note secrets. -/
def deriveCheckedProofPoints (key : ProvingKey.PinnedKey)
    (graph : WitnessVM.PinnedGraph) (circuit : WitnessVM.PinnedCircuit)
    (inputs : Array Nat) (commitment r s : Nat) :
    Except String (CheckedProofPoints circuit) :=
  match hw : WitnessVM.generateCheckedWitness graph circuit inputs commitment with
  | .error message => .error message
  | .ok witness =>
    match hd : ProvingKey.decodeFullKey key with
    | .error message => .error message
    | .ok decoded =>
      match hh : FrFFT.calculateH decoded.header.domainSize witness decoded.polsA decoded.polsB with
      | .error message => .error message
      | .ok h =>
        match hp : assembleParsed decoded witness h r s with
        | .error message => .error message
        | .ok points => .ok ⟨witness, points,
            WitnessVM.generateCheckedWitness_passes graph circuit inputs commitment witness hw,
            ⟨key, graph, inputs, commitment, r, s, decoded, h, hw, hd, hh, hp⟩⟩

/-- Success of the actual builder fixes every original derivation argument. -/
theorem derive_success_from_original (key : ProvingKey.PinnedKey)
    (graph : WitnessVM.PinnedGraph) (circuit : WitnessVM.PinnedCircuit)
    (inputs : Array Nat) (commitment r s : Nat) (result : CheckedProofPoints circuit)
    (success : deriveCheckedProofPoints key graph circuit inputs commitment r s = .ok result) :
    Derivation key graph circuit inputs commitment r s result.witness result.points := by
  unfold deriveCheckedProofPoints at success
  split at success
  · cases success
  · rename_i witness hw
    split at success
    · cases success
    · rename_i decoded hd
      split at success
      · cases success
      · rename_i h hh
        split at success
        · cases success
        · rename_i points hp
          cases success
          exact ⟨decoded, h, hw, hd, hh, hp⟩

theorem derived_points_have_construction (circuit : WitnessVM.PinnedCircuit)
    (result : CheckedProofPoints circuit) :
    ∃ key graph inputs commitment r s,
      Derivation key graph circuit inputs commitment r s result.witness result.points :=
  result.constructed

theorem derived_points_use_checked_witness (circuit : WitnessVM.PinnedCircuit)
    (result : CheckedProofPoints circuit) :
    Groth16R1CS.checkCircuit circuit.circuit result.witness = .ok 28275 :=
  result.checked

end Tornado.Protocol.Groth16MSM

#print axioms Tornado.Protocol.Groth16MSM.derived_points_use_checked_witness

#print axioms Tornado.Protocol.Groth16MSM.derive_success_from_original
#print axioms Tornado.Protocol.Groth16MSM.derived_points_have_construction
