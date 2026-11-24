import TornadoProofs.Witness.OperationFacts
import LeanCryptoProofs.BabyJubjub.MontgomeryDomains
import LeanCryptoProofs.BabyJubjub.NativeGroupPoint

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BN254Fr
open LeanCrypto.Proofs.BabyJubjubDomains LeanCrypto.Proofs.BabyJubjubPrimes

theorem montgomeryMeaning_nonzero (values : Array Nat) (reference : PointRef) (point : Point)
    (meaning : MontgomeryMeaning values reference point) : point ≠ 0 := by
  obtain ⟨equation,rfl⟩ := meaning
  exact montgomeryPoint_nonzero _ _ equation

theorem montgomeryMeaning_domains (values : Array Nat) (reference : PointRef) (point : Point)
    (meaning : MontgomeryMeaning values reference point) (torsion : subgroupOrder • point=0) :
    model values[reference.2]! ≠ 0 ∧ model values[reference.1]! ≠ 0 ∧ model values[reference.1]!+1 ≠ 0 := by
  obtain ⟨equation,equal⟩ := meaning
  let nonsingular : curve.Nonsingular (model values[reference.1]!) (model values[reference.2]!) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp ((montgomery_equation _ _).mp equation)
  have pointEqual : WeierstrassCurve.Affine.Point.some _ _ nonsingular=point := equal
  have killed : subgroupOrder • WeierstrassCurve.Affine.Point.some _ _ nonsingular=0 := by rw [pointEqual]; exact torsion
  exact ⟨montgomery_v_nonzero _ _ nonsingular killed,montgomery_u_nonzero _ _ nonsingular killed,
    montgomery_u_add_one_nonzero _ _ equation⟩

theorem montgomeryMeaning_separated (values : Array Nat) (firstRef secondRef : PointRef) (firstPoint secondPoint : Point)
    (firstMeaning : MontgomeryMeaning values firstRef firstPoint)
    (secondMeaning : MontgomeryMeaning values secondRef secondPoint)
    (different : firstPoint ≠ secondPoint) (opposite : firstPoint ≠ -secondPoint) :
    model values[firstRef.1]! ≠ model values[secondRef.1]! := by
  obtain ⟨first,firstEqual⟩ := firstMeaning
  obtain ⟨second,secondEqual⟩ := secondMeaning
  let firstNS : curve.Nonsingular (model values[firstRef.1]!) (model values[firstRef.2]!) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp ((montgomery_equation _ _).mp first)
  let secondNS : curve.Nonsingular (model values[secondRef.1]!) (model values[secondRef.2]!) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp ((montgomery_equation _ _).mp second)
  have firstSame : WeierstrassCurve.Affine.Point.some _ _ firstNS=firstPoint := firstEqual
  have secondSame : WeierstrassCurve.Affine.Point.some _ _ secondNS=secondPoint := secondEqual
  apply montgomery_u_separated _ _ _ _ firstNS secondNS
  · simpa only [firstSame,secondSame] using different
  · simpa only [firstSame,secondSame] using opposite

theorem edwardsMeaning_domains (values : Array Nat) (reference : PointRef) (point : Point)
    (meaning : EdwardsMeaning values reference point) (torsion : subgroupOrder • point=0) (nonzero : point ≠ 0) :
    model values[reference.1]! ≠ 0 ∧ 1-model values[reference.2]! ≠ 0 := by
  obtain ⟨equation,equal⟩ := meaning
  let ep : EPoint := ⟨model values[reference.1]!,model values[reference.2]!,equation⟩
  have pointEqual : toMontgomery ep=point := equal
  constructor
  · intro zero
    have same : ep.neg=ep := by
      apply epoint_ext
      · change -model values[reference.1]! = model values[reference.1]!
        simp only [zero,neg_zero]
      · rfl
    have negative : point= -point := by simpa only [same,pointEqual] using toMontgomery_neg ep
    have doubled : point+point=0 := by
      calc
        point+point=point+(-point) := congrArg (point+·) negative
        _=0 := add_neg_cancel point
    exact nonzero (odd_subgroup_no_two point torsion doubled)
  · apply sub_ne_zero.mpr
    intro same
    apply nonzero
    rw [←pointEqual,toMontgomery_zero_iff]
    exact same.symm

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.montgomeryMeaning_nonzero
#print axioms TornadoProofs.Witness.PedersenReference.montgomeryMeaning_domains
#print axioms TornadoProofs.Witness.PedersenReference.montgomeryMeaning_separated
#print axioms TornadoProofs.Witness.PedersenReference.edwardsMeaning_domains
