import TornadoProofs.Witness.NativeField
import Tornado.Protocol.TornadoWitness
import Init.Data.Range.Lemmas

open Lean Elab Term Meta in
elab "signatureLittleEndian" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `Tornado.Crypto.TornadoSignature `Tornado.Crypto.bytesToNatLE)

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.TornadoWitness
open Tornado.Crypto

abbrev nativeLittleEndian (bytes : ByteArray) : Nat := signatureLittleEndian bytes

def byteSum (bytes : ByteArray) (width : Nat) : Nat :=
  ((List.range width).map fun index => (bytes.get! index).toNat * 2^(8*index)).sum

theorem additive_forIn (items : List Nat) (initial : Nat) (valueAt : Nat → Nat) :
    (forIn items initial (fun index current => pure (.yield (current+valueAt index))) : Id Nat) =
      initial+(items.map valueAt).sum := by
  induction items generalizing initial with
  | nil =>
    simp
    rfl
  | cons head rest ih =>
    rw [List.forIn_cons]
    change (forIn rest (initial+valueAt head)
      (fun index current => pure (.yield (current+valueAt index))) : Id Nat) = _
    rw [ih]
    simp only [List.map_cons,List.sum_cons,Nat.add_assoc]

def littleEndianReference (bytes : ByteArray) : Nat := Id.run do
  let mut n := 0
  for i in [0:bytes.size] do
    n := n+(bytes.get! i).toNat*2^(8*i)
  return n

theorem nativeLittleEndian_reference (bytes : ByteArray) :
    nativeLittleEndian bytes=littleEndianReference bytes := rfl

theorem nativeLittleEndian_sum (bytes : ByteArray) :
    nativeLittleEndian bytes=byteSum bytes bytes.size := by
  rw [nativeLittleEndian_reference]
  change (forIn (Std.Legacy.Range.mk 0 bytes.size 1 (by decide)) 0
    (fun index current => pure (ForInStep.yield (current+(bytes.get! index).toNat*2^(8*index)))) : Id Nat) = _
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  rw [← List.range_eq_range',additive_forIn]
  simp only [byteSum,Nat.zero_add]

theorem byteSum_bound (bytes : ByteArray) (width : Nat) :
    byteSum bytes width<2^(8*width) := by
  induction width with
  | zero => simp [byteSum]
  | succ width ih =>
    simp only [byteSum,List.range_succ,List.map_append,List.sum_append,
      List.map_singleton,List.sum_singleton]
    change byteSum bytes width+(bytes.get! width).toNat*2^(8*width)<2^(8*(width+1))
    have byteBound : (bytes.get! width).toNat≤255 := by
      have bound := (bytes.get! width).toNat_lt
      omega
    have product := Nat.mul_le_mul_right (2^(8*width)) byteBound
    rw [Nat.mul_add,Nat.mul_one,Nat.pow_add]
    norm_num only
    omega

theorem nativeLittleEndian_bound (bytes : ByteArray) :
    nativeLittleEndian bytes<2^(8*bytes.size) := by
  rw [nativeLittleEndian_sum]
  exact byteSum_bound _ _

theorem note_nullifier_248 (note : TornadoSignatureNote)
    (width : note.nullifierBytes.size=31) : note.nullifier<2^248 := by
  have bounded := nativeLittleEndian_bound note.nullifierBytes
  simpa only [width] using bounded

theorem note_secret_248 (note : TornadoSignatureNote)
    (width : note.secretBytes.size=31) : note.secret<2^248 := by
  have bounded := nativeLittleEndian_bound note.secretBytes
  simpa only [width] using bounded

theorem note_nullifier_Fr (note : TornadoSignatureNote)
    (width : note.nullifierBytes.size=31) : note.nullifier<Field.q :=
  Nat.lt_trans (note_nullifier_248 note width) (by decide)

theorem note_secret_Fr (note : TornadoSignatureNote)
    (width : note.secretBytes.size=31) : note.secret<Field.q :=
  Nat.lt_trans (note_secret_248 note width) (by decide)

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.additive_forIn
#print axioms TornadoProofs.Witness.Source.nativeLittleEndian_reference
#print axioms TornadoProofs.Witness.Source.nativeLittleEndian_sum
#print axioms TornadoProofs.Witness.Source.byteSum_bound
#print axioms TornadoProofs.Witness.Source.nativeLittleEndian_bound
#print axioms TornadoProofs.Witness.Source.note_nullifier_248
#print axioms TornadoProofs.Witness.Source.note_secret_248
#print axioms TornadoProofs.Witness.Source.note_nullifier_Fr
#print axioms TornadoProofs.Witness.Source.note_secret_Fr
