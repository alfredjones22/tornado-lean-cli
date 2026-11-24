import LeanCryptoProofs.BabyJubjub.EdwardsPoint
import LeanCryptoProofs.BabyJubjub.TableSeparation

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjubDomains
open LeanCrypto.Proofs.BabyJubjub LeanCrypto.Proofs.BabyJubjubPrimes

variable {G : Type*} [AddCommGroup G]

theorem odd_subgroup_no_two (point : G) (torsion : subgroupOrder • point = 0)
    (double : point+point = 0) : point = 0 := by
  have odd : subgroupOrder = 2*((subgroupOrder-1)/2)+1 := by decide +kernel
  rw [odd,add_nsmul,mul_nsmul,two_nsmul,one_nsmul,double,nsmul_zero,zero_add] at torsion
  exact torsion

theorem montgomery_v_nonzero (u v : Field) (nonsingular : curve.Nonsingular u v)
    (torsion : subgroupOrder • (WeierstrassCurve.Affine.Point.some u v nonsingular) = 0) : v ≠ 0 := by
  intro zero
  have negative : v = curve.negY u v := by simp [zero,curve,WeierstrassCurve.Affine.negY]
  have double := WeierstrassCurve.Affine.Point.add_self_of_Y_eq (h₁ := nonsingular) negative
  have impossible := odd_subgroup_no_two _ torsion double
  cases impossible

theorem montgomery_u_nonzero (u v : Field) (nonsingular : curve.Nonsingular u v)
    (torsion : subgroupOrder • (WeierstrassCurve.Affine.Point.some u v nonsingular) = 0) : u ≠ 0 := by
  intro zero
  have equation := (montgomery_equation u v).2 nonsingular.1
  have squareZero : v^2 = 0 := by simpa [Montgomery,zero] using equation
  exact montgomery_v_nonzero u v nonsingular torsion (eq_zero_of_pow_eq_zero squareZero)

theorem montgomery_u_add_one_nonzero (u v : Field) (equation : Montgomery u v) : u+1 ≠ 0 := by
  intro zero
  have negative : u = -1 := eq_neg_of_add_eq_zero_left zero
  have square : v^2 = (168696 : Field) := by
    calc
      _ = u^3+168698*u^2+u := equation
      _ = 168696 := by rw [negative]; ring
  apply LeanCrypto.Proofs.BabyJubjubComplete.edwards_d_nonsquare
  exact ⟨v,by simpa only [pow_two] using square.symm⟩

theorem montgomery_u_separated (u1 v1 u2 v2 : Field)
    (first : curve.Nonsingular u1 v1) (second : curve.Nonsingular u2 v2)
    (different : WeierstrassCurve.Affine.Point.some u1 v1 first ≠
      WeierstrassCurve.Affine.Point.some u2 v2 second)
    (opposite : WeierstrassCurve.Affine.Point.some u1 v1 first ≠
      -(WeierstrassCurve.Affine.Point.some u2 v2 second)) : u1 ≠ u2 := by
  intro equal
  rcases WeierstrassCurve.Affine.Point.X_eq_iff.mp equal with same | negative
  · exact different same
  · exact opposite negative

end LeanCrypto.Proofs.BabyJubjubDomains
#print axioms LeanCrypto.Proofs.BabyJubjubDomains.odd_subgroup_no_two
#print axioms LeanCrypto.Proofs.BabyJubjubDomains.montgomery_v_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubDomains.montgomery_u_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubDomains.montgomery_u_add_one_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjubDomains.montgomery_u_separated
