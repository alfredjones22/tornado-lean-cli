import TornadoProofs.QapSource
import TornadoProofs.WorkerSampling

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TornadoProofs.PipelineComposition

open Tornado.Protocol LeanCrypto.Proofs.Groth16Assembly
open TornadoProofs.ProofObservation TornadoProofs.ProofPrivacy

/-- Composition evidence for original source stages. A separate witness
construction theorem must supply `witnessBuilt`; this structure does not
assert that arbitrary notes or remote replies satisfy those input rules. -/
structure ExecutionSource (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (context : Context) where
  inputs : Array Nat
  decoded : ProvingKey.ParsedKey
  inputBuilt : TornadoWitness.prepareInputPrefix withdrawal = .ok inputs
  inputSignals : inputs.extract 1 7 = (ClassicProofPipeline.ReviewedPublic.ofWithdrawal withdrawal).signals
  witnessBuilt : WitnessVM.generateCheckedWitness assets.graph assets.circuit inputs
    withdrawal.note.commitment = .ok context.witness
  keyBuilt : ProvingKey.decodeFullKey assets.key = .ok decoded
  hBuilt : FrFFT.calculateH decoded.header.domainSize context.witness decoded.polsA decoded.polsB = .ok context.h
  queryKey : context.key = Groth16MSM.QueryKey.fromParsed decoded
  nVars : decoded.header.nVars = 28300
  nPublic : decoded.header.nPublic = 6
  domain : decoded.header.domainSize = 32768
  hCount : decoded.hExps.size = 32767
  signals : context.signals = (ClassicProofPipeline.ReviewedPublic.ofWithdrawal withdrawal).signals

/-- Actual application derivation constructs checked points and their native
formula from the same original fixed source inputs; no accepted verifier or
point-assembly result is a premise. -/
theorem derive_construct (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (context : Context)
    (source : ExecutionSource assets withdrawal context) (r s : Nat)
    (rBound : r < LeanCrypto.BN254.G1.scalarPrime)
    (sBound : s < LeanCrypto.BN254.G1.scalarPrime) :
    ∃ checked : Groth16MSM.CheckedProofPoints assets.circuit,
      Groth16MSM.deriveCheckedProofPoints assets.key assets.graph assets.circuit source.inputs
        withdrawal.note.commitment r s = .ok checked ∧
      checked.points = construction context.key context.witness context.h r s := by
  have assembled := assemble_construct context.key context.witness context.h r s
    context.valid context.dimensions ⟨rBound, sBound, context.witnessCanonical, context.hCanonical⟩
  have parsed : Groth16MSM.assembleParsed source.decoded context.witness context.h r s =
      .ok (construction context.key context.witness context.h r s) := by
    unfold Groth16MSM.assembleParsed
    simp only [source.nVars, source.nPublic, source.domain, source.hCount,
      bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
      pure, Except.pure, bind, Except.bind]
    rw [← source.queryKey]
    exact assembled
  unfold Groth16MSM.deriveCheckedProofPoints
  split
  · rename_i message failed
    rw [source.witnessBuilt] at failed
    cases failed
  · rename_i witness generated
    have equal : witness = context.witness := Except.ok.inj (generated.symm.trans source.witnessBuilt)
    subst witness
    split
    · rename_i message failed
      rw [source.keyBuilt] at failed
      cases failed
    · rename_i decoded decodedBuilt
      have equal : decoded = source.decoded := Except.ok.inj (decodedBuilt.symm.trans source.keyBuilt)
      subst decoded
      split
      · rename_i message failed
        rw [source.hBuilt] at failed
        cases failed
      · rename_i h hBuilt
        have equal : h = context.h := Except.ok.inj (hBuilt.symm.trans source.hBuilt)
        subst h
        split
        · rename_i message failed
          rw [parsed] at failed
          cases failed
        · rename_i points pointsBuilt
          have equal : points = construction context.key context.witness context.h r s :=
            Except.ok.inj (pointsBuilt.symm.trans parsed)
          exact ⟨_, rfl, equal⟩

def publicObservation (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (r s : Nat) : Option (ByteArray × Array Nat) :=
  (ClassicProofPipeline.prove assets withdrawal r s).toOption.map
    (fun proof => (proof.bytes, proof.signals))

/-- The original full pipeline has exactly the constructed point observer,
including every possible normalization/serializer/verifier failure. This is
composition, conditional on the explicitly supplied original source stages. -/
theorem pipeline_observation (assets : ClassicProofPipeline.PinnedAssets)
    (withdrawal : TornadoWitness.WithdrawalInput) (context : Context)
    (source : ExecutionSource assets withdrawal context) (r s : Nat)
    (rPositive : 0 < r) (sPositive : 0 < s)
    (rBound : r < LeanCrypto.BN254.G1.scalarPrime)
    (sBound : s < LeanCrypto.BN254.G1.scalarPrime) :
    publicObservation assets withdrawal r s = context.native (some (r, s)) := by
  obtain ⟨checked, generated, formula⟩ := derive_construct assets withdrawal context source r s rBound sBound
  have rNonzero : (r == 0) = false := by simp [Nat.ne_of_gt rPositive]
  have sNonzero : (s == 0) = false := by simp [Nat.ne_of_gt sPositive]
  have rCanonical : decide (r ≥ BN254G1.scalarPrime) = false := by simp [Nat.not_le.mpr rBound]
  have sCanonical : decide (s ≥ BN254G1.scalarPrime) = false := by simp [Nat.not_le.mpr sBound]
  have sourceObserved := original_observation_eq_points assets.circuit checked
    (ClassicProofPipeline.ReviewedPublic.ofWithdrawal withdrawal).signals
  unfold publicObservation ClassicProofPipeline.prove ClassicProofPipeline.preparePublicProof
  simp only [rNonzero, sNonzero, rCanonical, sCanonical, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i message failed
    rw [source.inputBuilt] at failed
    cases failed
  · rename_i inputs inputsBuilt
    have equal : inputs = source.inputs := Except.ok.inj (inputsBuilt.symm.trans source.inputBuilt)
    subst inputs
    have prefixGuard : (source.inputs.extract 1 7 !=
        (ClassicProofPipeline.ReviewedPublic.ofWithdrawal withdrawal).signals) = false := by
      rw [source.inputSignals]
      simp only [bne_self_eq_false]
    simp only [prefixGuard, Bool.false_eq_true, ↓reduceDIte]
    split
    · rename_i message failed
      rw [generated] at failed
      cases failed
    · rename_i actual actualBuilt
      have equal : actual = checked := Except.ok.inj (actualBuilt.symm.trans generated)
      subst actual
      have canonical : Canonical context.witness context.h r s :=
        ⟨rBound, sBound, context.witnessCanonical, context.hCanonical⟩
      have built := assemble_construct context.key context.witness context.h r s context.valid context.dimensions canonical
      unfold Context.native
      dsimp only
      rw [built]
      dsimp only
      rw [← source.signals] at sourceObserved
      rw [← formula, ← sourceObserved]
      unfold originalObservation originalAcceptPoints
      rw [source.signals]
      split
      · rename_i message failed
        simp only [failed, Except.map, Except.toOption, Option.map_none]
      · rename_i result accepted
        simp only [accepted, Except.map, Except.toOption, Option.map_some]

end TornadoProofs.PipelineComposition

#print axioms TornadoProofs.PipelineComposition.derive_construct
#print axioms TornadoProofs.PipelineComposition.pipeline_observation
