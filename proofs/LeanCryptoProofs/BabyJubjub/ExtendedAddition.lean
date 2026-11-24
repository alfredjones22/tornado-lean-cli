import LeanCryptoProofs.BabyJubjub.NativeExtended
import LeanCryptoProofs.BabyJubjub.EdwardsAddition

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace LeanCrypto.Proofs.BabyJubjub

def addK (p q : RawPoint) : Field :=
  168696*normalizedX p*normalizedX q*normalizedY p*normalizedY q

theorem native_add_factors (p q : RawPoint) (first : Admissible p) (second : Admissible q) :
    addE p q = Z p*Z q*(normalizedX p*normalizedY q+normalizedY p*normalizedX q) ∧
    addF p q = Z p*Z q*(1-addK p q) ∧
    addG p q = Z p*Z q*(1+addK p q) ∧
    addH p q = Z p*Z q*(normalizedY p*normalizedY q-168700*normalizedX p*normalizedX q) := by
  have tp : T p=X p*Y p/Z p := (eq_div_iff first.1).2 first.2.1
  have tq : T q=X q*Y q/Z q := (eq_div_iff second.1).2 second.2.1
  unfold addE addF addG addH addK normalizedX normalizedY
  rw [tp,tq]
  refine ⟨?_,?_,?_,?_⟩ <;> field_simp [first.1,second.1]

theorem add_z_nonzero (p q : RawPoint) (first : Admissible p) (second : Admissible q) :
    Z (nativeAddPoints p q)≠0 := by
  have denominators := BabyJubjubComplete.babyjub_complete_denominators
    (normalizedX p) (normalizedY p) (normalizedX q) (normalizedY q)
    (normalized_curve p first) (normalized_curve q second)
  obtain ⟨_,f,g,_⟩ := native_add_factors p q first second
  rw [(native_add_coordinates p q).2.2.1,f,g]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero first.1 second.1) denominators.2)
    (mul_ne_zero (mul_ne_zero first.1 second.1) denominators.1)

theorem native_add_normalized (p q : RawPoint) (first : Admissible p) (second : Admissible q) :
    normalizedX (nativeAddPoints p q)=edwardsAddX (normalizedX p) (normalizedY p) (normalizedX q) (normalizedY q) ∧
    normalizedY (nativeAddPoints p q)=edwardsAddY (normalizedX p) (normalizedY p) (normalizedX q) (normalizedY q) := by
  have denominators := BabyJubjubComplete.babyjub_complete_denominators
    (normalizedX p) (normalizedY p) (normalizedX q) (normalizedY q)
    (normalized_curve p first) (normalized_curve q second)
  obtain ⟨e,f,g,h⟩ := native_add_factors p q first second
  obtain ⟨cx,cy,cz,_⟩ := native_add_coordinates p q
  unfold normalizedX normalizedY
  rw [cx,cy,cz,e,f,g,h]
  change
    ((Z p*Z q*(normalizedX p*normalizedY q+normalizedY p*normalizedX q))*(Z p*Z q*(1-addK p q)))/
      ((Z p*Z q*(1-addK p q))*(Z p*Z q*(1+addK p q))) = _ ∧
    ((Z p*Z q*(1+addK p q))*(Z p*Z q*(normalizedY p*normalizedY q-168700*normalizedX p*normalizedX q)))/
      ((Z p*Z q*(1-addK p q))*(Z p*Z q*(1+addK p q))) = _
  unfold edwardsAddX edwardsAddY
  change _ = (normalizedX p*normalizedY q+normalizedY p*normalizedX q)/(1+addK p q) ∧
    _ = (normalizedY p*normalizedY q-168700*normalizedX p*normalizedX q)/(1-addK p q)
  have positive : 1+addK p q≠0 := denominators.1
  have negative : 1-addK p q≠0 := denominators.2
  constructor <;> field_simp [first.1,second.1,positive,negative]

theorem homogeneous_of_normalized (p : RawPoint) (nonzero : Z p≠0)
    (relation : T p*Z p=X p*Y p) (curve : Edwards (normalizedX p) (normalizedY p)) :
    Admissible p := by
  refine ⟨nonzero,relation,?_⟩
  have product : T p=X p*Y p/Z p := (eq_div_iff nonzero).2 relation
  rw [product]
  unfold Edwards normalizedX normalizedY at curve
  field_simp [nonzero] at curve ⊢
  linear_combination curve

theorem add_admissible (p q : RawPoint) (first : Admissible p) (second : Admissible q) :
    Admissible (nativeAddPoints p q) := by
  have nonzero := add_z_nonzero p q first second
  have relation : T (nativeAddPoints p q)*Z (nativeAddPoints p q)=
      X (nativeAddPoints p q)*Y (nativeAddPoints p q) := by
    obtain ⟨cx,cy,cz,ct⟩ := native_add_coordinates p q
    rw [cx,cy,cz,ct]
    ring
  apply homogeneous_of_normalized _ nonzero relation
  obtain ⟨cx,cy⟩ := native_add_normalized p q first second
  rw [cx,cy]
  exact edwards_add_curve _ _ _ _ (normalized_curve p first) (normalized_curve q second)

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.native_add_factors
#print axioms LeanCrypto.Proofs.BabyJubjub.add_z_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjub.native_add_normalized
#print axioms LeanCrypto.Proofs.BabyJubjub.homogeneous_of_normalized
#print axioms LeanCrypto.Proofs.BabyJubjub.add_admissible
