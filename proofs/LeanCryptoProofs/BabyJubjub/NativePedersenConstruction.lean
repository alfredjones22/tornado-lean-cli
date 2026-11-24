import LeanCryptoProofs.BabyJubjub.NativePedersen

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BabyJubjubWindows

noncomputable def certifiedRaw (index : Nat) (receipt : LeanCrypto.Pedersen.CertifiedGenerator index) : RawPoint :=
  Classical.choose (certifiedGenerator_group index receipt)

theorem certifiedRaw_source (index : Nat) (receipt : LeanCrypto.Pedersen.CertifiedGenerator index) :
    nativeGenerator index=.ok (certifiedRaw index receipt) ∧ Admissible (certifiedRaw index receipt) ∧
      nativeAffine (certifiedRaw index receipt)=some (receipt.x,receipt.y) ∧
      groupPoint (certifiedRaw index receipt)≠0 ∧
      LeanCrypto.Proofs.BabyJubjubPrimes.subgroupOrder • groupPoint (certifiedRaw index receipt)=0 := by
  have accepted := Classical.choose_spec (certifiedGenerator_group index receipt)
  exact ⟨accepted.1,accepted.2.1,accepted.2.2.1,accepted.2.2.2.1,accepted.2.2.2.2.1⟩

noncomputable def receiptGenerators (input : ByteArray)
    (receipts : ∀ index, index < (input.size+24)/25 → LeanCrypto.Pedersen.CertifiedGenerator index)
    (index : Nat) : RawPoint :=
  if bound : index < (input.size+24)/25 then certifiedRaw index (receipts index bound) else nativeIdentity

theorem nativePedersenPoint_construct (input : ByteArray)
    (receipts : ∀ index, index < (input.size+24)/25 → LeanCrypto.Pedersen.CertifiedGenerator index) :
    ∃ result, nativePedersenPoint input=.ok result ∧ Admissible result ∧
      groupPoint result=((List.range' 0 ((input.size+24)/25)).map
        (fun index => nativeChunkAt input index • groupPoint (receiptGenerators input receipts index))).sum := by
  have inBounds (index : Nat) (member : index ∈ List.range' 0 ((input.size+24)/25)) :
      index < (input.size+24)/25 := by
    rcases List.mem_range'.mp member with ⟨position,bound,equal⟩
    omega
  have generated (index : Nat) (member : index ∈ List.range' 0 ((input.size+24)/25)) :
      nativeGenerator index=.ok (receiptGenerators input receipts index) := by
    have bound := inBounds index member
    simp only [receiptGenerators,dif_pos bound]
    exact (certifiedRaw_source index (receipts index bound)).1
  have valid (index : Nat) (member : index ∈ List.range' 0 ((input.size+24)/25)) :
      Admissible (receiptGenerators input receipts index) := by
    have bound := inBounds index member
    simp only [receiptGenerators,dif_pos bound]
    exact (certifiedRaw_source index (receipts index bound)).2.1
  obtain ⟨result,success,admitted,meaning⟩ := nativeFold_construct input _
    (receiptGenerators input receipts) generated valid
    (fun index member => nativeChunkAt_bounds input index (inBounds index member))
    nativeIdentity identity_admissible
  exact ⟨result,(nativePedersenPoint_source input).trans success,admitted,
    by simpa only [identity_groupPoint,zero_add] using meaning⟩

theorem nativePedersenX_construct (input : ByteArray)
    (receipts : ∀ index, index < (input.size+24)/25 → LeanCrypto.Pedersen.CertifiedGenerator index) :
    ∃ result, nativePedersenPoint input=.ok result ∧ Admissible result ∧
      LeanCrypto.pedersenX input=.ok (normalizedX result).val ∧
      groupPoint result=((List.range' 0 ((input.size+24)/25)).map
        (fun index => nativeChunkAt input index • groupPoint (receiptGenerators input receipts index))).sum := by
  obtain ⟨result,success,valid,meaning⟩ := nativePedersenPoint_construct input receipts
  refine ⟨result,success,valid,?_,meaning⟩
  unfold LeanCrypto.pedersenX
  change (do
    let point ← nativePedersenPoint input
    match nativeAffine point with
    | some (x,_) => pure x
    | none => throw "Invalid Pedersen result")=_
  rw [success]
  change (match nativeAffine result with
    | some (x,_) => Except.ok x
    | none => Except.error "Invalid Pedersen result")=_
  rw [native_affine_construct result valid]

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.certifiedRaw_source
#print axioms LeanCrypto.Proofs.BabyJubjub.nativePedersenPoint_construct
#print axioms LeanCrypto.Proofs.BabyJubjub.nativePedersenX_construct
