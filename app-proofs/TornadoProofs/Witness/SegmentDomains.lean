import TornadoProofs.Witness.WindowDomains
import TornadoProofs.Witness.SegmentBuilder
import LeanCryptoProofs.BabyJubjub.TableSeparation

set_option autoImplicit false
set_option maxRecDepth 10000
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubPrimes
open LeanCrypto.Proofs.BabyJubjubWindows

theorem order_zsmul_torsion (generator : Point) (order : addOrderOf generator=subgroupOrder) (scalar : Int) :
    subgroupOrder • (scalar • generator)=0 := by
  calc
    _ = (subgroupOrder:Int) • (scalar • generator) := (natCast_zsmul _ _).symm
    _ = scalar • ((subgroupOrder:Int) • generator) := smul_comm _ _ _
    _ = 0 := by rw [natCast_zsmul,←order,addOrderOf_nsmul_eq_zero,zsmul_zero]

theorem segment_generator_nonzero (generator : Point) (order : addOrderOf generator=subgroupOrder) :
    generator ≠ 0 := by
  have result := table_group_nonzero generator order 1 (by decide) (by norm_num) 0 (by decide)
  simpa only [pow_zero,mul_one,one_zsmul] using result

theorem segment_advance16_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (generator : Point)
    (order : addOrderOf generator=subgroupOrder) (index : Nat) (previous : PointRef)
    (meaning : MontgomeryMeaning values previous (8 • ((32:Int)^(index-1) • generator))) :
    BuildSpec (Execution.StepsAdmitted values) (doubled resolver previous)
      (fun result => MontgomeryMeaning values result (16 • ((32:Int)^(index-1) • generator))) := by
  have torsion : subgroupOrder • (8 • ((32:Int)^(index-1) • generator))=0 := by
    simpa only [mul_zsmul,ofNat_zsmul] using order_zsmul_torsion generator order (8*32^(index-1))
  simpa only [←add_nsmul,show (8+8:Nat)=16 from rfl] using
    doubled_torsion_spec resolver inputs values denotes previous _ meaning torsion

theorem segment_advance32_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (generator : Point)
    (order : addOrderOf generator=subgroupOrder) (index : Nat) (positive : 0 < index) (previous : PointRef)
    (meaning : MontgomeryMeaning values previous (16 • ((32:Int)^(index-1) • generator))) :
    BuildSpec (Execution.StepsAdmitted values) (doubled resolver previous)
      (fun result => MontgomeryMeaning values result ((32:Int)^index • generator)) := by
  have torsion : subgroupOrder • (16 • ((32:Int)^(index-1) • generator))=0 := by
    simpa only [mul_zsmul,ofNat_zsmul] using order_zsmul_torsion generator order (16*32^(index-1))
  have weight : (16 • ((32:Int)^(index-1) • generator))+(16 • ((32:Int)^(index-1) • generator))=
      (32:Int)^index • generator := by
    rw [←add_nsmul]
    change (32:Nat) • ((32:Int)^(index-1) • generator)=_
    rw [←natCast_zsmul,←mul_zsmul]
    have count : index=(index-1)+1 := by omega
    have power : (32:Int)^index=32*32^(index-1) := by
      conv_lhs => rw [count,pow_succ]
      ring
    rw [power]
    norm_num
  simpa only [weight] using doubled_torsion_spec resolver inputs values denotes previous _ meaning torsion

theorem segment_prefix_addition_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (generator : Point)
    (order : addOrderOf generator=subgroupOrder) (bits : Nat → Nat) (offset index : Nat)
    (small : index<50) (previous selected : PointRef)
    (firstMeaning : MontgomeryMeaning values previous (windowValue (digits bits offset index) • generator))
    (secondMeaning : MontgomeryMeaning values selected (digitAt bits offset index • ((32:Int)^index • generator))) :
    BuildSpec (Execution.StepsAdmitted values) (added resolver previous selected)
      (fun result => MontgomeryMeaning values result (windowValue (digits bits offset (index+1)) • generator)) := by
  have separated := prefix_highPlace_group_separated generator order (digits bits offset index)
    (digits_valid bits offset index) (digitAt bits offset index) (nibble_bounds _).1 (nibble_bounds _).2
    (by simpa only [digits_length] using small)
  simp only [digits_length,mul_zsmul] at separated
  have addition := added_separated_spec resolver inputs values denotes previous selected _ _
    firstMeaning secondMeaning separated.1 separated.2
  simpa only [prefix_group_succ] using addition

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.order_zsmul_torsion
#print axioms TornadoProofs.Witness.PedersenReference.segment_generator_nonzero
#print axioms TornadoProofs.Witness.PedersenReference.segment_advance16_spec
#print axioms TornadoProofs.Witness.PedersenReference.segment_advance32_spec
#print axioms TornadoProofs.Witness.PedersenReference.segment_prefix_addition_spec
