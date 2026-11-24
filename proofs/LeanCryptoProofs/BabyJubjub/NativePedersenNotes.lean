import LeanCryptoProofs.BabyJubjub.NativePedersenConstruction
import LeanCryptoProofs.BabyJubjub.TableSeparation

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
namespace LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BabyJubjubWindows

def firstThreeReceipts (first : LeanCrypto.Pedersen.CertifiedGenerator 0)
    (second : LeanCrypto.Pedersen.CertifiedGenerator 1) (third : LeanCrypto.Pedersen.CertifiedGenerator 2)
    (index : Nat) (bound : index<3) : LeanCrypto.Pedersen.CertifiedGenerator index := by
  match index with
  | 0 => exact first
  | 1 => exact second
  | 2 => exact third
  | index+3 => exact False.elim (by omega)

noncomputable def firstThreeGenerators (first : LeanCrypto.Pedersen.CertifiedGenerator 0)
    (second : LeanCrypto.Pedersen.CertifiedGenerator 1) (third : LeanCrypto.Pedersen.CertifiedGenerator 2)
    (index : Nat) : RawPoint :=
  if bound : index<3 then certifiedRaw index (firstThreeReceipts first second third index bound) else nativeIdentity

theorem nativePedersen_note_construct (input : ByteArray) (width : input.size=31 ∨ input.size=62)
    (first : LeanCrypto.Pedersen.CertifiedGenerator 0) (second : LeanCrypto.Pedersen.CertifiedGenerator 1)
    (third : LeanCrypto.Pedersen.CertifiedGenerator 2) :
    ∃ result, nativePedersenPoint input=.ok result ∧ Admissible result ∧
      LeanCrypto.pedersenX input=.ok (normalizedX result).val ∧
      groupPoint result=((List.range' 0 ((input.size+24)/25)).map
        (fun index => nativeChunkAt input index • groupPoint (firstThreeGenerators first second third index))).sum := by
  have count : (input.size+24)/25≤3 := by rcases width with width | width <;> simp only [width] <;> decide
  let receipts (index : Nat) (inside : index<(input.size+24)/25) :=
    firstThreeReceipts first second third index (lt_of_lt_of_le inside count)
  obtain ⟨result,success,valid,hashed,meaning⟩ := nativePedersenX_construct input receipts
  refine ⟨result,success,valid,hashed,meaning.trans ?_⟩
  apply congrArg List.sum
  apply List.map_congr_left
  intro index member
  rcases List.mem_range'.mp member with ⟨position,bound,equal⟩
  have inside : index<(input.size+24)/25 := by omega
  have three : index<3 := lt_of_lt_of_le inside count
  simp only [receiptGenerators,firstThreeGenerators,dif_pos inside,dif_pos three,receipts]

theorem nativePedersen_note_signed_sum (input : ByteArray) (width : input.size=31 ∨ input.size=62)
    (first : LeanCrypto.Pedersen.CertifiedGenerator 0) (second : LeanCrypto.Pedersen.CertifiedGenerator 1)
    (third : LeanCrypto.Pedersen.CertifiedGenerator 2) :
    ∃ result, nativePedersenPoint input=.ok result ∧ Admissible result ∧
      LeanCrypto.pedersenX input=.ok (normalizedX result).val ∧
      groupPoint result=((List.range' 0 ((input.size+24)/25)).map
        (fun index => windowValue (byteDigits
          (input.extract (index*25) (min ((index+1)*25) input.size)).data.toList) •
          groupPoint (firstThreeGenerators first second third index))).sum := by
  obtain ⟨result,success,valid,hashed,meaning⟩ := nativePedersen_note_construct input width first second third
  refine ⟨result,success,valid,hashed,meaning.trans ?_⟩
  apply congrArg List.sum
  apply List.map_congr_left
  intro index member
  rcases List.mem_range'.mp member with ⟨position,bound,equal⟩
  have inside : index<(input.size+24)/25 := by omega
  have count : (input.size+24)/25≤3 := by rcases width with width | width <;> simp only [width] <;> decide
  have three : index<3 := lt_of_lt_of_le inside count
  have order : addOrderOf (groupPoint (firstThreeGenerators first second third index))=
      LeanCrypto.Proofs.BabyJubjubPrimes.subgroupOrder := by
    simp only [firstThreeGenerators,dif_pos three]
    obtain ⟨point,generated,valid,affine,order,x,y⟩ :=
      certifiedGenerator_exact_order index (firstThreeReceipts first second third index three)
    have same : point=certifiedRaw index (firstThreeReceipts first second third index three) := by
      have generated' := (certifiedRaw_source index (firstThreeReceipts first second third index three)).1
      rw [generated] at generated'
      exact Except.ok.inj generated'
    simpa only [same] using order
  have size : (input.extract (index*25) (min ((index+1)*25) input.size)).size≤25 := by
    simp only [ByteArray.size_extract]
    omega
  have digitsSize : (byteDigits (input.extract (index*25) (min ((index+1)*25) input.size)).data.toList).length≤50 := by
    rw [byteDigits_length]
    change 2*(input.extract (index*25) (min ((index+1)*25) input.size)).size≤50
    omega
  dsimp only [nativeChunkAt]
  rw [nativeChunk_value]
  exact canonicalScalar_group _ order _ (bounded_window_scalar _ (byteDigits_valid _) digitsSize)

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.nativePedersen_note_construct
#print axioms LeanCrypto.Proofs.BabyJubjub.nativePedersen_note_signed_sum
