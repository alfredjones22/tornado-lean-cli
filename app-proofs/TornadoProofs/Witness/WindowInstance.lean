import TornadoProofs.Witness.WindowDomains

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubPrimes

/-- The actual public window compiler, with every curve/table denominator
discharged by the original generator's exact subgroup order and window bound.
Bit lookup and the selector/sign operations are supplied by their separate
source-level compiler refinements, rather than by final VM acceptance. -/
theorem compiler_window_group_spec (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Symbolic.Denotes resolver.nodes inputs values) (commitment : Bool)
    (generator : Point) (order : addOrderOf generator=subgroupOrder)
    (exponent : Nat) (size : exponent < 50) (offset : Nat) (first : PointRef)
    (meaning : MontgomeryMeaning values first ((32^exponent:Nat) • generator))
    (bits : Nat → Nat) (bitRelation : Nat → Nat → Prop)
    (bitSpec : ∀ position,BuildSpec (Execution.StepsAdmitted values)
      ((compilerWindows resolver commitment).bit position) (fun result => bitRelation result (bits position)))
    (selection : ∀ b0 b1 b2 table,bitRelation b0 (bits offset) → bitRelation b1 (bits (offset+1)) →
      bitRelation b2 (bits (offset+2)) →
      TableMeaning (MontgomeryMeaning values) ((32^exponent:Nat) • generator) 8 table →
      BuildSpec (Execution.StepsAdmitted values) ((compilerWindows resolver commitment).choose b0 b1 b2 table)
        (fun result => MontgomeryMeaning values result
          ((PedersenWindows.selectorIndex (bits offset) (bits (offset+1)) (bits (offset+2))+1) •
            ((32^exponent:Nat) • generator))))
    (signing : ∀ point sign,MontgomeryMeaning values point
        ((PedersenWindows.selectorIndex (bits offset) (bits (offset+1)) (bits (offset+2))+1) •
          ((32^exponent:Nat) • generator)) →
      bitRelation sign (bits (offset+3)) →
      BuildSpec (Execution.StepsAdmitted values) ((compilerWindows resolver commitment).signed point sign)
        (fun result => MontgomeryMeaning values result
          (PedersenWindows.selectedWindow ((32^exponent:Nat) • generator)
            (bits offset) (bits (offset+1)) (bits (offset+2)) (bits (offset+3))))) :
    BuildSpec (Execution.StepsAdmitted values) (window resolver commitment offset first)
      (fun result => MontgomeryMeaning values result.1
          (PedersenWindows.selectedWindow ((32^exponent:Nat) • generator)
            (bits offset) (bits (offset+1)) (bits (offset+2)) (bits (offset+3))) ∧
        MontgomeryMeaning values result.2 (8 • ((32^exponent:Nat) • generator))) := by
  rw [compiler_window_eq]
  apply windowWith_buildSpec (Execution.StepsAdmitted values) (MontgomeryMeaning values) bitRelation
    (compilerWindows resolver commitment) bits offset _ first meaning
  · exact window_doubled_spec resolver inputs values denotes generator order exponent first meaning
  · intro index lower upper previous previousMeaning
    exact window_table_addition_spec resolver inputs values denotes generator order exponent size first meaning
      index lower upper previous previousMeaning
  · exact bitSpec
  · exact selection
  · exact signing

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.compiler_window_group_spec
