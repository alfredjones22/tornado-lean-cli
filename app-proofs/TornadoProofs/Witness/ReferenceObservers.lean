import TornadoProofs.Witness.NativeReferenceObserver
import TornadoProofs.Witness.ReferenceConstruction

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.TornadoWitness

/-- The group observers of the original bytes determine the actual returned
canonical DAG coordinates, including identity sums handled by complete Edwards addition. -/
theorem reference_group_coordinates (input : WithdrawalInput) (source : Source.ValidWithdrawal input)
    (values : Array Nat) (canonical : Primitive.Bounded values)
    (first : LeanCrypto.Pedersen.CertifiedGenerator 0) (second : LeanCrypto.Pedersen.CertifiedGenerator 1)
    (third : LeanCrypto.Pedersen.CertifiedGenerator 2) (commitment nullifier : PointRef)
    (commitmentMeaning : EdwardsMeaning values commitment
      (nativeCommitmentGroup input.note.preimage (generatorGroup first second third)))
    (nullifierMeaning : EdwardsMeaning values nullifier
      (nativeNullifierGroup input.note.nullifierBytes (generatorGroup first second third))) :
    values[commitment.1]! =input.note.commitment ∧ values[nullifier.1]! =input.note.nullifierHash := by
  have width : input.note.preimage.size=62 := by
    change (input.note.nullifierBytes++input.note.secretBytes).size=62
    rw [ByteArray.size_append,source.nullifierWidth,source.secretWidth]
  obtain ⟨commitmentRaw,_,commitmentValid,commitmentHash,commitmentGroup⟩ :=
    native_commitment_group input.note.preimage width first second third
  obtain ⟨nullifierRaw,_,nullifierValid,nullifierHash,nullifierGroup⟩ :=
    native_nullifier_group input.note.nullifierBytes source.nullifierWidth first second third
  have commitmentObserved := edwardsMeaning_normalized_x values commitment commitmentRaw commitmentValid
    (Primitive.bounded_get values canonical commitment.1) (by rw [commitmentGroup]; exact commitmentMeaning)
  have nullifierObserved := edwardsMeaning_normalized_x values nullifier nullifierRaw nullifierValid
    (Primitive.bounded_get values canonical nullifier.1) (by rw [nullifierGroup]; exact nullifierMeaning)
  have commitmentIdentity : (normalizedX commitmentRaw).val=input.note.commitment :=
    Except.ok.inj (commitmentHash.symm.trans source.commitment)
  have nullifierIdentity : (normalizedX nullifierRaw).val=input.note.nullifierHash :=
    Except.ok.inj (nullifierHash.symm.trans source.nullifier)
  exact ⟨commitmentObserved.trans commitmentIdentity,nullifierObserved.trans nullifierIdentity⟩

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.reference_group_coordinates
