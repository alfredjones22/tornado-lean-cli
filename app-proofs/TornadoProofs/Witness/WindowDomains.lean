import TornadoProofs.Witness.BuilderDomains
import TornadoProofs.Witness.WindowBuilder

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubPrimes
open LeanCrypto.Proofs.BabyJubjubWindows

theorem natural_weight_zsmul (generator : Point) (coefficient exponent : Nat) :
    ((coefficient:Int)*32^exponent) • generator=coefficient • ((32^exponent:Nat) • generator) := by
  have power : (32:Int)^exponent=((32^exponent:Nat):Int) := (Int.natCast_pow 32 exponent).symm
  rw [mul_zsmul,power,natCast_zsmul,natCast_zsmul]

theorem window_base_torsion (generator : Point) (order : addOrderOf generator=subgroupOrder) (exponent : Nat) :
    subgroupOrder • ((32^exponent:Nat) • generator)=0 := by
  rw [←mul_nsmul,Nat.mul_comm,mul_nsmul,←order,addOrderOf_nsmul_eq_zero,nsmul_zero]

theorem window_table_separated (generator : Point) (order : addOrderOf generator=subgroupOrder)
    (exponent : Nat) (size : exponent < 50) (index : Nat) (lower : 2 ≤ index) (upper : index < 8) :
    (32^exponent:Nat) • generator ≠ index • ((32^exponent:Nat) • generator) ∧
      (32^exponent:Nat) • generator ≠ -(index • ((32^exponent:Nat) • generator)) := by
  have separated := table_group_separated generator order 1 (index:Int) (by norm_num) (by norm_num)
    (by omega) (by omega) (by omega) exponent size
  have power : (32:Int)^exponent=((32^exponent:Nat):Int) := (Int.natCast_pow 32 exponent).symm
  simpa only [one_mul,power,mul_zsmul,natCast_zsmul] using separated

theorem window_doubled_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (generator : Point)
    (order : addOrderOf generator=subgroupOrder) (exponent : Nat) (first : PointRef)
    (meaning : MontgomeryMeaning values first ((32^exponent:Nat) • generator)) :
    BuildSpec (Execution.StepsAdmitted values) (doubled resolver first)
      (fun result => MontgomeryMeaning values result (2 • ((32^exponent:Nat) • generator))) := by
  simpa only [two_nsmul] using doubled_torsion_spec resolver inputs values denotes first _ meaning
    (window_base_torsion generator order exponent)

theorem window_table_addition_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (generator : Point)
    (order : addOrderOf generator=subgroupOrder) (exponent : Nat) (size : exponent < 50) (first : PointRef)
    (meaning : MontgomeryMeaning values first ((32^exponent:Nat) • generator))
    (index : Nat) (lower : 2 ≤ index) (upper : index < 8) (previous : PointRef)
    (previousMeaning : MontgomeryMeaning values previous (index • ((32^exponent:Nat) • generator))) :
    BuildSpec (Execution.StepsAdmitted values) (added resolver first previous)
      (fun result => MontgomeryMeaning values result ((index+1) • ((32^exponent:Nat) • generator))) := by
  obtain ⟨different,opposite⟩ := window_table_separated generator order exponent size index lower upper
  have addition := added_separated_spec resolver inputs values denotes first previous _ _ meaning previousMeaning different opposite
  simpa only [add_nsmul,one_nsmul,add_comm] using addition

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.natural_weight_zsmul
#print axioms TornadoProofs.Witness.PedersenReference.window_base_torsion
#print axioms TornadoProofs.Witness.PedersenReference.window_table_separated
#print axioms TornadoProofs.Witness.PedersenReference.window_doubled_spec
#print axioms TornadoProofs.Witness.PedersenReference.window_table_addition_spec
