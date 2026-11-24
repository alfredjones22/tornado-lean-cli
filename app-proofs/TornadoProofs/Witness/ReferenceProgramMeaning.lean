import TornadoProofs.Witness.ActualSegment
import TornadoProofs.Witness.ProgramBuilder
import TornadoProofs.Witness.BaseCoordinates
import TornadoProofs.Witness.GeneratorGroupOrder
import TornadoProofs.Witness.ReferenceObservers

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule
open Tornado.Protocol.WitnessSymbolic Tornado.Protocol.TornadoWitness
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubWindows

/-- Original valid note/path facts and authenticated public generators
construct the arithmetic meaning of every operation in the original schedule.
No final witness, VM acceptance, or R1CS checker is assumed. -/
theorem referenceMeaning_construct (resolver : Resolver) (graph : Tornado.Protocol.WitnessVM.SelectedGraph)
    (input : WithdrawalInput) (source : Source.ValidWithdrawal input) (valid : tableValid resolver.nodes=true)
    (certified : CertifiedPedersenBases graph) : Source.ReferenceMeaning resolver graph input := by
  let values := Execution.sourceValues resolver (inputPrefix input) input.note.commitment
  let generators := generatorGroup certified.first certified.second certified.third
  have denotes := Execution.sourceValues_denotes resolver (inputPrefix input) input.note.commitment valid
  have canonical := Execution.sourceValues_bounded resolver (inputPrefix input) input.note.commitment valid
    (Source.valid_prefix_canonical input source) (Source.valid_commitment_canonical input source)
  intro reference compiled
  obtain ⟨bases,width,program,baseMeaning⟩ := referenceSchedule_base_meaning resolver graph
    ((inputPrefix input).push input.note.commitment) values denotes certified reference compiled
  have segmentSpec (commitment : Bool) (offset windows index : Nat) (positive : 0 < windows)
      (bounded : windows ≤ 50) (indexBound : index < 3) :
      BuildSpec (Execution.StepsAdmitted values)
        (segmentWith (compilerOps resolver commitment) offset windows bases[index]!)
        (fun result => EdwardsMeaning values result
          (windowValue (digits (noteBits input commitment) offset windows) • generators index)) := by
    rw [←compiler_segment_eq]
    exact actual_segment_source_spec resolver input source valid commitment (generators index)
      (generatorGroup_exact_order certified.first certified.second certified.third index indexBound)
      offset windows positive bounded bases[index]! (baseMeaning index indexBound)
  have composed := programWith_buildSpec (Execution.StepsAdmitted values) (EdwardsMeaning values)
    (compilerOps resolver true) (compilerOps resolver false) bases width
    (windowValue (digits (noteBits input true) 0 50) • generators 0)
    (windowValue (digits (noteBits input true) 200 50) • generators 1)
    (windowValue (digits (noteBits input true) 400 24) • generators 2)
    (windowValue (digits (noteBits input false) 0 50) • generators 0)
    (windowValue (digits (noteBits input false) 200 12) • generators 1)
    (segmentSpec true 0 50 0 (by decide) (by decide) (by decide))
    (segmentSpec true 200 50 1 (by decide) (by decide) (by decide))
    (segmentSpec true 400 24 2 (by decide) (by decide) (by decide))
    (segmentSpec false 0 50 0 (by decide) (by decide) (by decide))
    (segmentSpec false 200 12 1 (by decide) (by decide) (by decide))
    (fun first second p q firstMeaning secondMeaning =>
      babyAdded_spec resolver ((inputPrefix input).push input.note.commitment) values denotes
        first second p q firstMeaning secondMeaning)
    (fun first second p q firstMeaning secondMeaning =>
      babyAdded_spec resolver ((inputPrefix input).push input.note.commitment) values denotes
        first second p q firstMeaning secondMeaning)
  rw [compiler_program_eq] at program
  have empty : Execution.StepsAdmitted values #[] := by
    intro step member
    simp only [Array.not_mem_empty] at member
  obtain ⟨admitted,commitmentMeaning,nullifierMeaning⟩ := composed #[]
    (reference.commitment,reference.nullifier) reference.steps empty program
  have commitment : EdwardsMeaning values reference.commitment (nativeCommitmentGroup input.note.preimage generators) :=
    commitmentMeaning
  have nullifier : EdwardsMeaning values reference.nullifier (nativeNullifierGroup input.note.nullifierBytes generators) :=
    nullifierMeaning
  exact ⟨admitted,reference_group_coordinates input source values canonical
    certified.first certified.second certified.third reference.commitment reference.nullifier commitment nullifier⟩

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.referenceMeaning_construct
