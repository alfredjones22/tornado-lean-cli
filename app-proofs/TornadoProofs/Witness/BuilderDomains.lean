import TornadoProofs.Witness.EdwardsBuilder
import TornadoProofs.Witness.MeaningDomains

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubPrimes

/-- Odd-subgroup membership discharges the native doubling denominator. -/
theorem doubled_torsion_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (reference : PointRef) (point : Point)
    (meaning : MontgomeryMeaning values reference point) (torsion : subgroupOrder • point=0) :
    BuildSpec (Execution.StepsAdmitted values) (doubled resolver reference)
      (fun result => MontgomeryMeaning values result (point+point)) :=
  doubled_spec resolver inputs values denotes reference point meaning
    (montgomeryMeaning_domains values reference point meaning torsion).1

/-- Group separation discharges the original Montgomery x-difference guard. -/
theorem added_separated_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (firstRef secondRef : PointRef) (firstPoint secondPoint : Point)
    (firstMeaning : MontgomeryMeaning values firstRef firstPoint)
    (secondMeaning : MontgomeryMeaning values secondRef secondPoint)
    (different : firstPoint ≠ secondPoint) (opposite : firstPoint ≠ -secondPoint) :
    BuildSpec (Execution.StepsAdmitted values) (added resolver firstRef secondRef)
      (fun result => MontgomeryMeaning values result (firstPoint+secondPoint)) :=
  added_spec resolver inputs values denotes firstRef secondRef firstPoint secondPoint firstMeaning secondMeaning
    (montgomeryMeaning_separated values firstRef secondRef firstPoint secondPoint firstMeaning secondMeaning different opposite)

theorem toMontgomery_torsion_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (commitment : Bool)
    (reference : PointRef) (point : Point) (meaning : EdwardsMeaning values reference point)
    (torsion : subgroupOrder • point=0) (nonzero : point ≠ 0) :
    BuildSpec (Execution.StepsAdmitted values) ((compilerOps resolver commitment).toMontgomery reference)
      (fun result => MontgomeryMeaning values result point) :=
  let domains := edwardsMeaning_domains values reference point meaning torsion nonzero
  toMontgomery_spec resolver inputs values denotes commitment reference point meaning domains.1 domains.2

theorem toEdwards_torsion_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (commitment : Bool)
    (reference : PointRef) (point : Point) (meaning : MontgomeryMeaning values reference point)
    (torsion : subgroupOrder • point=0) :
    BuildSpec (Execution.StepsAdmitted values) ((compilerOps resolver commitment).toEdwards reference)
      (fun result => EdwardsMeaning values result point) :=
  let domains := montgomeryMeaning_domains values reference point meaning torsion
  toEdwards_spec resolver inputs values denotes commitment reference point meaning domains.1 domains.2.2

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.doubled_torsion_spec
#print axioms TornadoProofs.Witness.PedersenReference.added_separated_spec
#print axioms TornadoProofs.Witness.PedersenReference.toMontgomery_torsion_spec
#print axioms TornadoProofs.Witness.PedersenReference.toEdwards_torsion_spec
