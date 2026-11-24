import LeanCryptoProofs.BabyJubjub.DoubleGroup

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace LeanCrypto.Proofs.BabyJubjub

def EPoint.torsionTwo : EPoint := ⟨0,-1,by norm_num [Edwards]⟩
def EPoint.flip (p : EPoint) : EPoint := ⟨-p.x,-p.y,by simpa only [Edwards,neg_sq] using p.onCurve⟩

def torsionTwo : Point := WeierstrassCurve.Affine.Point.mk ((montgomery_equation 0 0).mp (by norm_num [Montgomery]))

theorem epoint_add_torsionTwo (p : EPoint) : p.add EPoint.torsionTwo=p.flip := by
  apply epoint_ext <;> simp [EPoint.add,EPoint.torsionTwo,EPoint.flip,edwardsAddX,edwardsAddY]

theorem toMontgomery_torsionTwo : toMontgomery EPoint.torsionTwo=torsionTwo := by
  simp only [toMontgomery,EPoint.torsionTwo,show (-1:Field)≠1 from by decide +kernel,↓reduceDIte]
  simp only [chartV,chartU,add_neg_cancel,zero_div]
  rfl

theorem torsion_math_coordinates (p : EPoint) (nonzeroX : p.x≠0) (finite : p.y≠1) :
    curve.addX (chartU p.y) 0 (curve.slope (chartU p.y) 0 (chartV p.x p.y) 0)=chartU (-p.y) ∧
    curve.addY (chartU p.y) 0 (chartV p.x p.y) (curve.slope (chartU p.y) 0 (chartV p.x p.y) 0)=chartV (-p.x) (-p.y) := by
  have plus := regular_plus_nonzero p nonzeroX
  have minus : 1-p.y≠0 := sub_ne_zero.mpr finite.symm
  have uNonzero : chartU p.y≠0 := div_ne_zero plus minus
  have slope : curve.slope (chartU p.y) 0 (chartV p.x p.y) 0=1/p.x := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne uNonzero]
    simp only [sub_zero,chartV]
    field_simp [uNonzero,nonzeroX]
  have xEquation : curve.addX (chartU p.y) 0 (curve.slope (chartU p.y) 0 (chartV p.x p.y) 0)=chartU (-p.y) := by
    rw [slope]
    simp only [WeierstrassCurve.Affine.addX,curve,zero_mul,add_zero,sub_zero]
    unfold chartU
    field_simp [nonzeroX,plus,minus]
    have equation := p.onCurve
    unfold Edwards at equation
    linear_combination -equation
  refine ⟨xEquation,?_⟩
  simp only [WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,curve,zero_mul,sub_zero]
  dsimp only [curve] at xEquation slope
  rw [xEquation,slope]
  unfold chartV
  field_simp [nonzeroX]
  ring

theorem toMontgomery_add_torsionTwo_regular (p : EPoint) (nonzeroX : p.x≠0) (finite : p.y≠1) :
    toMontgomery (p.add EPoint.torsionTwo)=toMontgomery p+torsionTwo := by
  have plus := regular_plus_nonzero p nonzeroX
  have minus : 1-p.y≠0 := sub_ne_zero.mpr finite.symm
  have uNonzero : chartU p.y≠0 := div_ne_zero plus minus
  have sourceEquation := (montgomery_equation _ _).mp (chart_curve _ _ p.onCurve finite)
  let sourceNonsingular : curve.Nonsingular (chartU p.y) (chartV p.x p.y) :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp sourceEquation
  let targetNonsingular : curve.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp ((montgomery_equation 0 0).mp (by norm_num [Montgomery]))
  have source : toMontgomery p=WeierstrassCurve.Affine.Point.some (chartU p.y) (chartV p.x p.y) sourceNonsingular := by
    simp only [toMontgomery,finite,↓reduceDIte,WeierstrassCurve.Affine.Point.mk]
  have target : torsionTwo=WeierstrassCurve.Affine.Point.some 0 0 targetNonsingular := rfl
  have finiteFlip : p.flip.y≠1 := by
    intro equal
    have bad : p.y= -1 := by change -p.y=1 at equal; linear_combination -equal
    exact nonzeroX (edwards_y_neg_one _ _ p.onCurve bad)
  have addition := WeierstrassCurve.Affine.Point.add_of_X_ne
    (h₁:=sourceNonsingular) (h₂:=targetNonsingular) uNonzero
  rw [epoint_add_torsionTwo,source,target,addition,toMontgomery,dif_neg finiteFlip]
  simp only [WeierstrassCurve.Affine.Point.mk]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨(torsion_math_coordinates p nonzeroX finite).1.symm,
    (torsion_math_coordinates p nonzeroX finite).2.symm⟩

theorem toMontgomery_add_torsionTwo (p : EPoint) :
    toMontgomery (p.add EPoint.torsionTwo)=toMontgomery p+torsionTwo := by
  by_cases infinite : p.y=1
  · have identity : p=EPoint.identity := epoint_ext _ _ (edwards_y_one _ _ p.onCurve infinite) infinite
    subst p
    rw [epoint_identity_add,toMontgomery_identity,zero_add,toMontgomery_torsionTwo]
  by_cases xZero : p.x=0
  · have yNeg : p.y= -1 := (edwards_x_zero _ _ p.onCurve xZero).resolve_left infinite
    have equal : p=EPoint.torsionTwo := epoint_ext _ _ xZero yNeg
    subst p
    simpa only [toMontgomery_torsionTwo] using toMontgomery_double EPoint.torsionTwo
  · exact toMontgomery_add_torsionTwo_regular p xZero infinite

theorem chartU_injective (y w : Field) (finiteY : y≠1) (finiteW : w≠1)
    (equal : chartU y=chartU w) : y=w := by
  have cross := (div_eq_div_iff (sub_ne_zero.mpr finiteY.symm) (sub_ne_zero.mpr finiteW.symm)).1 equal
  have product : (2:Field)*(y-w)=0 := by linear_combination cross
  exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left (by decide +kernel))

theorem epoint_eq_or_neg_of_chartU (p q : EPoint) (finiteP : p.y≠1) (finiteQ : q.y≠1)
    (equal : chartU p.y=chartU q.y) : p=q ∨ p=q.neg := by
  have yEqual := chartU_injective p.y q.y finiteP finiteQ equal
  have first := p.onCurve
  have second := q.onCurve
  rw [←yEqual] at second
  unfold Edwards at first second
  have product : (168700-168696*p.y^2)*(p.x^2-q.x^2)=0 := by linear_combination first-second
  have squares := sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left (edwards_coefficient_nonzero _ _ p.onCurve))
  rcases eq_or_eq_neg_of_sq_eq_sq p.x q.x squares with same | opposite
  · exact Or.inl (epoint_ext _ _ same yEqual)
  · exact Or.inr (epoint_ext _ _ opposite yEqual)

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.epoint_add_torsionTwo
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_torsionTwo
#print axioms LeanCrypto.Proofs.BabyJubjub.torsion_math_coordinates
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_add_torsionTwo_regular
#print axioms LeanCrypto.Proofs.BabyJubjub.toMontgomery_add_torsionTwo
#print axioms LeanCrypto.Proofs.BabyJubjub.chartU_injective
#print axioms LeanCrypto.Proofs.BabyJubjub.epoint_eq_or_neg_of_chartU
