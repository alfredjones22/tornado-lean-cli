import TornadoProofs.Witness.OperationFacts
import TornadoProofs.Witness.NibbleChunks
import LeanCryptoProofs.BabyJubjub.NativePedersenNotes
import LeanCryptoProofs.BabyJubjub.ChartInjective

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr
open LeanCrypto.Proofs.BabyJubjubWindows
open Tornado.Protocol.WitnessVM

noncomputable def generatorGroup (first : LeanCrypto.Pedersen.CertifiedGenerator 0)
    (second : LeanCrypto.Pedersen.CertifiedGenerator 1) (third : LeanCrypto.Pedersen.CertifiedGenerator 2)
    (index : Nat) : Point := groupPoint (firstThreeGenerators first second third index)

noncomputable def nativeCommitmentGroup (bytes : ByteArray) (generators : Nat → Point) : Point :=
  windowValue (digits (bitValue (Source.nativeLittleEndian bytes)) 0 50) • generators 0+
  windowValue (digits (bitValue (Source.nativeLittleEndian bytes)) 200 50) • generators 1+
  windowValue (digits (bitValue (Source.nativeLittleEndian bytes)) 400 24) • generators 2

noncomputable def nativeNullifierGroup (bytes : ByteArray) (generators : Nat → Point) : Point :=
  windowValue (digits (bitValue (Source.nativeLittleEndian bytes)) 0 50) • generators 0+
  windowValue (digits (bitValue (Source.nativeLittleEndian bytes)) 200 12) • generators 1

theorem native_commitment_group (bytes : ByteArray) (width : bytes.size=62)
    (first : LeanCrypto.Pedersen.CertifiedGenerator 0) (second : LeanCrypto.Pedersen.CertifiedGenerator 1)
    (third : LeanCrypto.Pedersen.CertifiedGenerator 2) :
    ∃ result, nativePedersenPoint bytes=.ok result ∧ Admissible result ∧
      LeanCrypto.pedersenX bytes=.ok (normalizedX result).val ∧
      groupPoint result=nativeCommitmentGroup bytes (generatorGroup first second third) := by
  obtain ⟨result,constructed,valid,hashed,meaning⟩ := nativePedersen_note_signed_sum bytes (Or.inr width) first second third
  refine ⟨result,constructed,valid,hashed,?_⟩
  rw [width] at meaning
  change groupPoint result=
    windowValue (byteDigits (bytes.extract 0 25).data.toList) • generatorGroup first second third 0+
    (windowValue (byteDigits (bytes.extract 25 50).data.toList) • generatorGroup first second third 1+
    (windowValue (byteDigits (bytes.extract 50 62).data.toList) • generatorGroup first second third 2+0)) at meaning
  obtain ⟨firstDigits,secondDigits,thirdDigits⟩ := Source.note62_chunk_digits bytes width
  rw [←firstDigits,←secondDigits,←thirdDigits] at meaning
  simpa only [nativeCommitmentGroup,add_zero,add_assoc] using meaning

theorem native_nullifier_group (bytes : ByteArray) (width : bytes.size=31)
    (first : LeanCrypto.Pedersen.CertifiedGenerator 0) (second : LeanCrypto.Pedersen.CertifiedGenerator 1)
    (third : LeanCrypto.Pedersen.CertifiedGenerator 2) :
    ∃ result, nativePedersenPoint bytes=.ok result ∧ Admissible result ∧
      LeanCrypto.pedersenX bytes=.ok (normalizedX result).val ∧
      groupPoint result=nativeNullifierGroup bytes (generatorGroup first second third) := by
  obtain ⟨result,constructed,valid,hashed,meaning⟩ := nativePedersen_note_signed_sum bytes (Or.inl width) first second third
  refine ⟨result,constructed,valid,hashed,?_⟩
  rw [width] at meaning
  change groupPoint result=
    windowValue (byteDigits (bytes.extract 0 25).data.toList) • generatorGroup first second third 0+
    (windowValue (byteDigits (bytes.extract 25 31).data.toList) • generatorGroup first second third 1+0) at meaning
  obtain ⟨firstDigits,secondDigits⟩ := Source.note31_chunk_digits bytes width
  rw [←firstDigits,←secondDigits] at meaning
  simpa only [nativeNullifierGroup,add_zero] using meaning

theorem edwardsMeaning_normalized_x (values : Array Nat) (reference : Nat×Nat) (raw : RawPoint)
    (valid : Admissible raw) (bounded : values[reference.1]! < Q)
    (meaning : EdwardsMeaning values reference (groupPoint raw)) :
    values[reference.1]! = (normalizedX raw).val := by
  obtain ⟨curve,equal⟩ := meaning
  have same := toMontgomery_injective (equal.trans (groupPoint_admitted raw valid))
  have x : model values[reference.1]! = normalizedX raw := congrArg EPoint.x same
  apply canonical_injective bounded (normalizedX raw).val_lt
  simpa only [model_val] using x

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.native_commitment_group
#print axioms TornadoProofs.Witness.PedersenReference.native_nullifier_group
#print axioms TornadoProofs.Witness.PedersenReference.edwardsMeaning_normalized_x
