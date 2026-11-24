import TornadoProofs.Witness.SegmentInstance
import TornadoProofs.Witness.ActualWindow

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule Tornado.Protocol.WitnessSymbolic Tornado.Protocol.TornadoWitness
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubPrimes
open LeanCrypto.Proofs.BabyJubjubWindows

/-- The original source note determines the complete segment; all bit,
selector, sign, curve-chart and prefix-addition domains are proved here. -/
theorem actual_segment_source_spec (resolver : Resolver) (input : WithdrawalInput)
    (source : Source.ValidWithdrawal input) (valid : tableValid resolver.nodes=true)
    (commitment : Bool) (generator : Point) (order : addOrderOf generator=subgroupOrder)
    (offset windows : Nat) (positive : 0 < windows) (bounded : windows ≤ 50) (first : PointRef)
    (meaning : EdwardsMeaning (Execution.sourceValues resolver (inputPrefix input) input.note.commitment) first generator) :
    BuildSpec (Execution.StepsAdmitted (Execution.sourceValues resolver (inputPrefix input) input.note.commitment))
      (segment resolver commitment offset windows first)
      (fun result => EdwardsMeaning (Execution.sourceValues resolver (inputPrefix input) input.note.commitment) result
        (windowValue (digits (noteBits input commitment) offset windows) • generator)) := by
  let values := Execution.sourceValues resolver (inputPrefix input) input.note.commitment
  have denotes := Execution.sourceValues_denotes resolver (inputPrefix input) input.note.commitment valid
  apply compiler_segment_group_spec resolver ((inputPrefix input).push input.note.commitment) values denotes commitment
    generator order (noteBits input commitment) offset windows positive bounded first meaning
  intro index upper point pointMeaning
  change BuildSpec (Execution.StepsAdmitted values)
    (windowWith (compilerWindows resolver commitment) (offset+4*index) point) _
  rw [←compiler_window_eq]
  have weighted : ((32^index:Nat) • generator)=(32:Int)^index • generator := by
    rw [←natCast_zsmul]
    congr 1
  have naturalMeaning : MontgomeryMeaning values point ((32^index:Nat) • generator) := by
    rw [weighted]
    exact pointMeaning
  have selected := actual_window_source_spec resolver input source valid commitment generator order index
    (by omega) (offset+4*index) point naturalMeaning
  have observed := PedersenWindows.selectedWindow_nativeNibble ((32:Int)^index • generator)
    (noteBits input commitment (offset+4*index)) (noteBits input commitment (offset+4*index+1))
    (noteBits input commitment (offset+4*index+2)) (noteBits input commitment (offset+4*index+3))
    (noteBits_binary input commitment _) (noteBits_binary input commitment _)
    (noteBits_binary input commitment _) (noteBits_binary input commitment _)
  simpa only [weighted,observed,digitAt] using selected

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.actual_segment_source_spec
