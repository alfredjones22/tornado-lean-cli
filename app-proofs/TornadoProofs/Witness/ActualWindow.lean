import TornadoProofs.Witness.WindowInstance
import TornadoProofs.Witness.BitBuilder
import TornadoProofs.Witness.ChoiceBuilder
import TornadoProofs.Witness.SignBuilder

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic
open Tornado.Protocol.TornadoWitness
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubPrimes

/-- Original note bytes determine every selector and sign in the actual
public compiler. No bit, selection, sign, or denominator refinement remains
as a supplied success/specification premise in this endpoint. -/
theorem actual_window_source_spec (resolver : Resolver) (input : WithdrawalInput)
    (source : Source.ValidWithdrawal input) (valid : tableValid resolver.nodes=true)
    (commitment : Bool) (generator : Point) (order : addOrderOf generator=subgroupOrder)
    (exponent : Nat) (size : exponent < 50) (offset : Nat) (first : PointRef)
    (meaning : MontgomeryMeaning (Execution.sourceValues resolver (inputPrefix input) input.note.commitment)
      first ((32^exponent:Nat) • generator)) :
    BuildSpec (Execution.StepsAdmitted (Execution.sourceValues resolver (inputPrefix input) input.note.commitment))
      (window resolver commitment offset first)
      (fun result => MontgomeryMeaning (Execution.sourceValues resolver (inputPrefix input) input.note.commitment) result.1
          (PedersenWindows.selectedWindow ((32^exponent:Nat) • generator)
            (noteBits input commitment offset) (noteBits input commitment (offset+1))
            (noteBits input commitment (offset+2)) (noteBits input commitment (offset+3))) ∧
        MontgomeryMeaning (Execution.sourceValues resolver (inputPrefix input) input.note.commitment) result.2
          (8 • ((32^exponent:Nat) • generator))) := by
  let values := Execution.sourceValues resolver (inputPrefix input) input.note.commitment
  have denotes := Execution.sourceValues_denotes resolver (inputPrefix input) input.note.commitment valid
  apply compiler_window_group_spec resolver ((inputPrefix input).push input.note.commitment) values denotes
    commitment generator order exponent size offset first meaning (noteBits input commitment) (BitMeaning values)
  · intro position
    exact bit_spec resolver input source valid commitment position
  · intro b0 b1 b2 table firstBit secondBit thirdBit tableMeaning
    exact choose_spec resolver ((inputPrefix input).push input.note.commitment) values denotes commitment
      b0 b1 b2 _ _ _ table _ firstBit secondBit thirdBit
      (noteBits_binary input commitment offset) (noteBits_binary input commitment (offset+1))
      (noteBits_binary input commitment (offset+2)) tableMeaning
  · intro reference sign selected signMeaning
    simpa only [PedersenWindows.selectedWindow] using
      signed_spec resolver ((inputPrefix input).push input.note.commitment) values denotes commitment reference _ sign
        (noteBits input commitment (offset+3)) selected signMeaning (noteBits_binary input commitment (offset+3))

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.actual_window_source_spec
