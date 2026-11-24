import TornadoProofs.Witness.SegmentDomains
import TornadoProofs.Witness.ReferenceCompiler

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubPrimes
open LeanCrypto.Proofs.BabyJubjubWindows

theorem compiler_segment_group_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (commitment : Bool)
    (generator : Point) (order : addOrderOf generator=subgroupOrder) (bits : Nat → Nat)
    (offset windows : Nat) (positive : 0 < windows) (bounded : windows ≤ 50) (first : PointRef)
    (meaning : EdwardsMeaning values first generator)
    (windowRefinement : ∀ index,index < windows → ∀ point,
      MontgomeryMeaning values point ((32:Int)^index • generator) →
      BuildSpec (Execution.StepsAdmitted values) (windowWith (compilerOps resolver commitment).windows (offset+4*index) point)
        (fun result => MontgomeryMeaning values result.1 (digitAt bits offset index • ((32:Int)^index • generator)) ∧
          MontgomeryMeaning values result.2 (8 • ((32:Int)^index • generator)))) :
    BuildSpec (Execution.StepsAdmitted values) (segment resolver commitment offset windows first)
      (fun result => EdwardsMeaning values result (windowValue (digits bits offset windows) • generator)) := by
  rw [compiler_segment_eq]
  apply segmentWith_buildSpec (Execution.StepsAdmitted values) (EdwardsMeaning values) (MontgomeryMeaning values)
    (compilerOps resolver commitment) bits offset windows generator first positive
  · exact toMontgomery_torsion_spec resolver inputs values denotes commitment first generator meaning
      (by simpa only [one_zsmul] using order_zsmul_torsion generator order 1)
      (segment_generator_nonzero generator order)
  · intro index _ _ previous previousMeaning
    exact segment_advance16_spec resolver inputs values denotes generator order index previous previousMeaning
  · intro index indexPositive _ previous previousMeaning
    exact segment_advance32_spec resolver inputs values denotes generator order index indexPositive previous previousMeaning
  · intro index upper point pointMeaning
    exact windowRefinement index upper point pointMeaning
  · intro index _ upper previous selected previousMeaning selectedMeaning
    exact segment_prefix_addition_spec resolver inputs values denotes generator order bits offset index (by omega)
      previous selected previousMeaning selectedMeaning
  · intro point pointMeaning
    exact toEdwards_torsion_spec resolver inputs values denotes commitment point _ pointMeaning
      (order_zsmul_torsion generator order _)

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.compiler_segment_group_spec
