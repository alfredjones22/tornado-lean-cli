import TornadoProofs.Witness.VerificationSource
import Tornado.Protocol.ClassicProofPipeline

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Tornado.Protocol.TornadoWitness
open TornadoProofs.Witness.Execution

theorem valid_sibling_scan (input : WithdrawalInput) (source : ValidWithdrawal input) :
    input.proof.siblings.any (· >= Tornado.Protocol.Groth16R1CS.scalarPrime)=false := by
  apply Array.any_eq_false.mpr
  intro index bound
  have canonical := source.siblings input.proof.siblings[index] (Array.getElem_mem bound)
  simpa only [decide_eq_true_eq] using Nat.not_le.mpr canonical

/-- The original note preimages, expected root, public fields, directions,
and native parent chain construct success of the actual input boundary. -/
theorem prepareInputPrefix_construct (input : WithdrawalInput) (source : ValidWithdrawal input) :
    prepareInputPrefix input=.ok (inputPrefix input) := by
  have expected : ¬input.expectedRoot >= Tornado.Protocol.Groth16R1CS.scalarPrime := Nat.not_le.mpr source.expectedCanonical
  have recipient : ¬input.recipient >= 2^160 := Nat.not_le.mpr source.recipient
  have relayer : ¬input.relayer >= 2^160 := Nat.not_le.mpr source.relayer
  have fee : ¬input.fee >= Tornado.Protocol.Groth16R1CS.scalarPrime := Nat.not_le.mpr source.fee
  have refund : ¬input.refund >= Tornado.Protocol.Groth16R1CS.scalarPrime := Nat.not_le.mpr source.refund
  have siblingScan := valid_sibling_scan input source
  simp only [source.siblingWidth] at siblingScan
  simp only [prepareInputPrefix,source.nullifierWidth,source.secretWidth,source.siblingWidth,source.directionWidth,
    bne_self_eq_false,Bool.false_or,Bool.false_eq_true,↓reduceIte,source.expectedRoot,expected,recipient,relayer,
    fee,refund,decide_false,siblingScan,source.commitment,source.nullifier,
    valid_membership_construct input source,Bool.not_true,bind,Except.bind,pure,Except.pure]

theorem inputPrefix_reviewed_signals (input : WithdrawalInput) (source : ValidWithdrawal input) :
    (inputPrefix input).extract 1 7 =
      (Tornado.Protocol.ClassicProofPipeline.ReviewedPublic.ofWithdrawal input).signals := by
  apply Array.toList_inj.mp
  simp [inputPrefix,source.expectedRoot,
    Tornado.Protocol.ClassicProofPipeline.ReviewedPublic.ofWithdrawal,
    Tornado.Protocol.ClassicProofPipeline.ReviewedPublic.signals]

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.valid_sibling_scan
#print axioms TornadoProofs.Witness.Source.prepareInputPrefix_construct
#print axioms TornadoProofs.Witness.Source.inputPrefix_reviewed_signals
