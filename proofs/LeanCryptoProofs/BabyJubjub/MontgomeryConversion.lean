import LeanCryptoProofs.BabyJubjub.DoubleGroup
import LeanCryptoProofs.BabyJubjub.MontgomeryPoint

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub

def fromMontX (u v : Field) : Field := u/v
def fromMontY (u : Field) : Field := (u-1)/(u+1)

theorem fromMont_curve (u v : Field) (equation : Montgomery u v) (nonzeroV : v≠0) (chart : u+1≠0) :
    Edwards (fromMontX u v) (fromMontY u) := by
  unfold Edwards fromMontX fromMontY
  field_simp [nonzeroV,chart]
  unfold Montgomery at equation
  linear_combination -(4*u)*equation

theorem fromMont_chart (u v : Field) (equation : Montgomery u v) (nonzeroV : v≠0) (chart : u+1≠0) :
    chartU (fromMontY u)=u ∧ chartV (fromMontX u v) (fromMontY u)=v ∧ fromMontY u≠1 := by
  have nonzeroU : u≠0 := by intro zero; exact nonzeroV (montgomery_zero_x u v equation zero)
  have two : (2:Field)≠0 := by decide +kernel
  have difference : u+1-(u-1)≠0 := by convert two using 1; ring
  have uEquation : chartU (fromMontY u)=u := by
    unfold fromMontY
    rw [fraction_chartU _ _ chart difference]
    apply (div_eq_iff difference).2
    ring
  have vEquation : chartV (fromMontX u v) (fromMontY u)=v := by
    unfold chartV fromMontX
    rw [uEquation]
    field_simp [nonzeroU,nonzeroV]
  have finite : fromMontY u≠1 := by
    intro one
    have equal := (div_eq_one_iff_eq chart).1 one
    apply two
    linear_combination -equal
  exact ⟨uEquation,vEquation,finite⟩

theorem fromMont_group (u v : Field) (equation : Montgomery u v) (nonzeroV : v≠0) (chart : u+1≠0) :
    toMontgomery ⟨fromMontX u v,fromMontY u,fromMont_curve u v equation nonzeroV chart⟩=
      montgomeryPoint u v equation := by
  obtain ⟨uEquation,vEquation,finite⟩ := fromMont_chart u v equation nonzeroV chart
  rw [toMontgomery,dif_neg finite]
  simp only [montgomeryPoint,WeierstrassCurve.Affine.Point.mk]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨uEquation,vEquation⟩

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.fromMont_curve
#print axioms LeanCrypto.Proofs.BabyJubjub.fromMont_chart
#print axioms LeanCrypto.Proofs.BabyJubjub.fromMont_group
