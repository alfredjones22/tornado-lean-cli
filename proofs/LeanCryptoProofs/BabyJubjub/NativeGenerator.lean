import LeanCryptoProofs.BabyJubjub.ScalarGroup
import LeanCryptoProofs.BabyJubjub.Primes
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BN254Fr
open LeanCrypto.Proofs.BabyJubjubPrimes

abbrev nativeGenerator (index : Nat) : Except String RawPoint :=
  (pedersenFieldPrivate LeanCrypto.generator) index

/-- A genuine public receipt supplies the exact deterministic native generator
and mathematical point/order facts. No generator-success oracle is an input. -/
theorem certifiedGenerator_group (index : Nat) (certified : LeanCrypto.Pedersen.CertifiedGenerator index) :
    ∃ point : RawPoint, nativeGenerator index=.ok point ∧ Admissible point ∧
      nativeAffine point=some (certified.x,certified.y) ∧ groupPoint point≠0 ∧
      subgroupOrder • groupPoint point=0 ∧
      normalizedX point=model certified.x ∧ normalizedY point=model certified.y := by
  obtain ⟨point,generated,admitted,affine,nontrivial,order⟩ := LeanCrypto.Pedersen.certifiedGenerator_accepted index certified
  change nativeGenerator index=.ok point at generated
  change nativeAffine point=some (certified.x,certified.y) at affine
  change nativeAffine (nativeScalarMul point subgroupOrder)=some (0,1) at order
  have valid := generator_admissible point admitted
  have nonzero : groupPoint point≠0 := by
    intro zero
    have identity := (native_affine_identity_iff point valid).mpr zero
    rw [affine] at identity
    have equal : (certified.x,certified.y)=(0,1) := Option.some.inj identity
    exact nontrivial.elim (fun x => x (congrArg Prod.fst equal)) (fun y => y (congrArg Prod.snd equal))
  have killed : subgroupOrder • groupPoint point=0 := by
    rw [←scalarMul_groupPoint point subgroupOrder valid]
    apply (native_affine_identity_iff _ (scalarMul_admissible point subgroupOrder valid)).mp
    exact order
  have coordinates := (Option.some.inj ((native_affine_construct point valid).symm.trans affine))
  have x := congrArg (fun pair : Nat×Nat => model pair.1) coordinates
  have y := congrArg (fun pair : Nat×Nat => model pair.2) coordinates
  refine ⟨point,generated,valid,affine,nonzero,killed,?_,?_⟩
  · simpa only [model_val] using x
  · simpa only [model_val] using y

/-- Checked unreduced L-multiplication, nonidentity, and the closed numerical
primality certificate establish the exact order of each admitted generator. -/
theorem certifiedGenerator_exact_order (index : Nat) (certified : LeanCrypto.Pedersen.CertifiedGenerator index) :
    ∃ point : RawPoint, nativeGenerator index=.ok point ∧ Admissible point ∧
      nativeAffine point=some (certified.x,certified.y) ∧ addOrderOf (groupPoint point)=subgroupOrder ∧
      normalizedX point=model certified.x ∧ normalizedY point=model certified.y := by
  obtain ⟨point,generated,valid,affine,nonzero,killed,x,y⟩ := certifiedGenerator_group index certified
  letI : Fact subgroupOrder.Prime := ⟨native_subgroup_order_prime⟩
  exact ⟨point,generated,valid,affine,addOrderOf_eq_prime killed nonzero,x,y⟩

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.certifiedGenerator_group
#print axioms LeanCrypto.Proofs.BabyJubjub.certifiedGenerator_exact_order
