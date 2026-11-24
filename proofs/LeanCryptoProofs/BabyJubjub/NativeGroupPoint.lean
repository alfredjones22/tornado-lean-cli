import LeanCryptoProofs.BabyJubjub.ScalarAdmission
import LeanCryptoProofs.BabyJubjub.EdwardsBasic

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BN254Fr

theorem toMontgomery_zero_iff (point : EPoint) : toMontgomery point=0 ↔ point.y=1 := by
  constructor
  · intro zero
    by_contra finite
    rw [toMontgomery,dif_neg finite] at zero
    cases zero
  · intro infinite
    simp only [toMontgomery,infinite,↓reduceDIte]

def normalizedPoint (point : RawPoint) (admitted : Admissible point) : EPoint :=
  ⟨normalizedX point,normalizedY point,normalized_curve point admitted⟩

noncomputable def groupPoint (point : RawPoint) : Point :=
  if admitted : Admissible point then toMontgomery (normalizedPoint point admitted) else 0

theorem groupPoint_admitted (point : RawPoint) (admitted : Admissible point) :
    groupPoint point=toMontgomery (normalizedPoint point admitted) := by
  simp only [groupPoint,dif_pos admitted]

theorem normalizedPoint_add (p q : RawPoint) (first : Admissible p) (second : Admissible q) :
    normalizedPoint (nativeAddPoints p q) (add_admissible p q first second)=
      (normalizedPoint p first).add (normalizedPoint q second) := by
  obtain ⟨x,y⟩ := native_add_normalized p q first second
  apply epoint_ext
  · exact x
  · exact y

theorem identity_groupPoint : groupPoint nativeIdentity=0 := by
  rw [groupPoint_admitted _ identity_admissible,toMontgomery_zero_iff]
  change normalizedY nativeIdentity=1
  change (1:Field)/(1:Field)=1
  exact div_self one_ne_zero

theorem groupPoint_zero_iff (point : RawPoint) (admitted : Admissible point) :
    groupPoint point=0 ↔ normalizedY point=1 := by
  rw [groupPoint_admitted point admitted,toMontgomery_zero_iff]
  rfl

theorem native_affine_identity_iff (point : RawPoint) (admitted : Admissible point) :
    nativeAffine point=some (0,1) ↔ groupPoint point=0 := by
  rw [native_affine_construct point admitted,groupPoint_zero_iff point admitted]
  constructor
  · intro equal
    have y : (normalizedY point).val=1 := congrArg Prod.snd (Option.some.inj equal)
    have represented := congrArg model y
    simpa only [model_val,show model 1=(1:Field) from rfl] using represented
  · intro y
    have x := edwards_y_one _ _ (normalized_curve point admitted) y
    rw [x,y]
    decide +kernel

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_zero_iff
#print axioms LeanCrypto.Proofs.BabyJubjub.groupPoint_admitted
#print axioms LeanCrypto.Proofs.BabyJubjub.normalizedPoint_add
#print axioms LeanCrypto.Proofs.BabyJubjub.identity_groupPoint
#print axioms LeanCrypto.Proofs.BabyJubjub.groupPoint_zero_iff
#print axioms LeanCrypto.Proofs.BabyJubjub.native_affine_identity_iff
