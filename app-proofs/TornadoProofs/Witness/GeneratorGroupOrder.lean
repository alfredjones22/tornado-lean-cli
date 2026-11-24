import TornadoProofs.Witness.NativeReferenceObserver

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubPrimes

theorem generatorGroup_exact_order (first : LeanCrypto.Pedersen.CertifiedGenerator 0)
    (second : LeanCrypto.Pedersen.CertifiedGenerator 1) (third : LeanCrypto.Pedersen.CertifiedGenerator 2)
    (index : Nat) (bound : index < 3) :
    addOrderOf (generatorGroup first second third index)=subgroupOrder := by
  unfold generatorGroup firstThreeGenerators
  rw [dif_pos bound]
  let receipt := firstThreeReceipts first second third index bound
  obtain ⟨point,generated,valid,affine,order,x,y⟩ := certifiedGenerator_exact_order index receipt
  have generated' := (certifiedRaw_source index receipt).1
  rw [generated] at generated'
  have same : point=certifiedRaw index receipt := Except.ok.inj generated'
  simpa only [same] using order

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.generatorGroup_exact_order
