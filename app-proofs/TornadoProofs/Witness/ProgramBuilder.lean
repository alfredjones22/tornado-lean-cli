import TornadoProofs.Witness.SegmentBuilder

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule
open LeanCrypto.Proofs.BabyJubjubWindows

theorem programWith_buildSpec {G : Type} [AddCommGroup G]
    (invariant : Array Footprint → Prop) (relation : PointRef → G → Prop)
    (commitment nullifier : ReferenceOps Builder PointRef PointRef Nat) (bases : Array PointRef)
    (width : bases.size=3) (c0 c1 c2 n0 n1 : G)
    (firstCommitment : BuildSpec invariant (segmentWith commitment 0 50 bases[0]!) (fun result => relation result c0))
    (secondCommitment : BuildSpec invariant (segmentWith commitment 200 50 bases[1]!) (fun result => relation result c1))
    (thirdCommitment : BuildSpec invariant (segmentWith commitment 400 24 bases[2]!) (fun result => relation result c2))
    (firstNullifier : BuildSpec invariant (segmentWith nullifier 0 50 bases[0]!) (fun result => relation result n0))
    (secondNullifier : BuildSpec invariant (segmentWith nullifier 200 12 bases[1]!) (fun result => relation result n1))
    (commitmentAdd : ∀ first second p q,relation first p → relation second q →
      BuildSpec invariant (commitment.babyAdded first second) (fun result => relation result (p+q)))
    (nullifierAdd : ∀ first second p q,relation first p → relation second q →
      BuildSpec invariant (nullifier.babyAdded first second) (fun result => relation result (p+q))) :
    BuildSpec invariant (programWith commitment nullifier bases)
      (fun result => relation result.1 (c0+c1+c2) ∧ relation result.2 (n0+n1)) := by
  unfold programWith
  simp only [width,bne_self_eq_false,Bool.false_eq_true,if_false,pure_bind]
  apply buildSpec_bind invariant _ _ _ _ firstCommitment
  intro first firstMeaning
  apply buildSpec_bind invariant _ _ _ _ secondCommitment
  intro second secondMeaning
  apply buildSpec_bind invariant _ _ _ _ thirdCommitment
  intro third thirdMeaning
  apply buildSpec_bind invariant _ _ _ _ (commitmentAdd first second c0 c1 firstMeaning secondMeaning)
  intro combined combinedMeaning
  apply buildSpec_bind invariant _ _ _ _ (commitmentAdd combined third (c0+c1) c2 combinedMeaning thirdMeaning)
  intro commitmentPoint commitmentMeaning
  apply buildSpec_bind invariant _ _ _ _ firstNullifier
  intro nullifierFirst nullifierFirstMeaning
  apply buildSpec_bind invariant _ _ _ _ secondNullifier
  intro nullifierSecond nullifierSecondMeaning
  apply buildSpec_bind invariant _ _ _ _ (nullifierAdd nullifierFirst nullifierSecond n0 n1 nullifierFirstMeaning nullifierSecondMeaning)
  intro nullifierPoint nullifierMeaning
  exact buildSpec_pure invariant (commitmentPoint,nullifierPoint) _ ⟨commitmentMeaning,nullifierMeaning⟩

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.programWith_buildSpec
