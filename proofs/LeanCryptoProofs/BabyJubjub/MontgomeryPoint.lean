import LeanCryptoProofs.BabyJubjub.Montgomery
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub

def montgomeryPoint (u v : Field) (equation : Montgomery u v) : Point :=
  WeierstrassCurve.Affine.Point.mk ((by
    simpa only [Montgomery,WeierstrassCurve.Affine.equation_iff,curve,zero_mul,add_zero,one_mul] using equation) : curve.Equation u v)

def montgomerySlope (u v z w : Field) : Field := (w-v)/(z-u)
def montgomeryAddU (u v z w : Field) : Field := (montgomerySlope u v z w)^2-168698-u-z
def montgomeryAddV (u v z w : Field) : Field := montgomerySlope u v z w*(u-montgomeryAddU u v z w)-v

def montgomeryDoubleSlope (u v : Field) : Field := (3*u^2+337396*u+1)/(2*v)
def montgomeryDoubleU (u v : Field) : Field := (montgomeryDoubleSlope u v)^2-168698-2*u
def montgomeryDoubleV (u v : Field) : Field := montgomeryDoubleSlope u v*(u-montgomeryDoubleU u v)-v

theorem montgomeryPoint_nonzero (u v : Field) (equation : Montgomery u v) :
    montgomeryPoint u v equation≠0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem montgomery_add_construct (u v z w : Field) (first : Montgomery u v) (second : Montgomery z w)
    (different : u≠z) :
    ∃ equation : Montgomery (montgomeryAddU u v z w) (montgomeryAddV u v z w),
      montgomeryPoint _ _ equation=montgomeryPoint u v first+montgomeryPoint z w second := by
  let h1 : curve.Nonsingular u v := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (by simpa only [WeierstrassCurve.Affine.equation_iff,curve,zero_mul,add_zero,one_mul] using first)
  let h2 : curve.Nonsingular z w := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (by simpa only [WeierstrassCurve.Affine.equation_iff,curve,zero_mul,add_zero,one_mul] using second)
  have slope : curve.slope u z v w=montgomerySlope u v z w := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne different]
    unfold montgomerySlope
    apply (div_eq_div_iff (sub_ne_zero.mpr different) (sub_ne_zero.mpr different.symm)).2
    ring
  have x : curve.addX u z (curve.slope u z v w)=montgomeryAddU u v z w := by
    rw [slope]
    simp only [WeierstrassCurve.Affine.addX,curve,zero_mul,add_zero,montgomeryAddU]
  have y : curve.addY u z v (curve.slope u z v w)=montgomeryAddV u v z w := by
    rw [slope]
    simp only [WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.negY,curve,zero_mul,add_zero,sub_zero,
      montgomeryAddV,montgomeryAddU]
    ring
  have ns := WeierstrassCurve.Affine.nonsingular_add h1 h2 (fun equal => different equal.1)
  have equation : Montgomery (montgomeryAddU u v z w) (montgomeryAddV u v z w) := by
    rw [←x,←y]
    simpa only [Montgomery,WeierstrassCurve.Affine.equation_iff,curve,zero_mul,add_zero,one_mul] using ns.1
  refine ⟨equation,?_⟩
  have addition := WeierstrassCurve.Affine.Point.add_of_X_ne (h₁:=h1) (h₂:=h2) different
  unfold montgomeryPoint
  simp only [WeierstrassCurve.Affine.Point.mk]
  rw [addition,WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨x.symm,y.symm⟩

theorem montgomery_double_construct (u v : Field) (first : Montgomery u v) (nonzero : v≠0) :
    ∃ equation : Montgomery (montgomeryDoubleU u v) (montgomeryDoubleV u v),
      montgomeryPoint _ _ equation=montgomeryPoint u v first+montgomeryPoint u v first := by
  let h : curve.Nonsingular u v := WeierstrassCurve.Affine.equation_iff_nonsingular.mp
    (by simpa only [WeierstrassCurve.Affine.equation_iff,curve,zero_mul,add_zero,one_mul] using first)
  have opposite : v≠curve.negY u v := by
    simp only [WeierstrassCurve.Affine.negY,curve,zero_mul,sub_zero]
    intro equal
    exact (mul_ne_zero (by decide +kernel : (2:Field)≠0) nonzero) (by linear_combination equal)
  have slope : curve.slope u u v v=montgomeryDoubleSlope u v := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl opposite]
    simp only [WeierstrassCurve.Affine.negY,curve,zero_mul,sub_zero]
    unfold montgomeryDoubleSlope
    congr 1
    ring
  have x : curve.addX u u (curve.slope u u v v)=montgomeryDoubleU u v := by
    rw [slope]
    simp only [WeierstrassCurve.Affine.addX,curve,zero_mul,add_zero,montgomeryDoubleU]
    ring
  have y : curve.addY u u v (curve.slope u u v v)=montgomeryDoubleV u v := by
    rw [slope]
    simp only [WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.negY,curve,zero_mul,add_zero,sub_zero,
      montgomeryDoubleV,montgomeryDoubleU]
    ring
  have ns := WeierstrassCurve.Affine.nonsingular_add h h (fun pair => opposite pair.2)
  have equation : Montgomery (montgomeryDoubleU u v) (montgomeryDoubleV u v) := by
    rw [←x,←y]
    simpa only [Montgomery,WeierstrassCurve.Affine.equation_iff,curve,zero_mul,add_zero,one_mul] using ns.1
  refine ⟨equation,?_⟩
  have addition := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁:=h) opposite
  unfold montgomeryPoint
  simp only [WeierstrassCurve.Affine.Point.mk]
  rw [addition,WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨x.symm,y.symm⟩

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.montgomeryPoint_nonzero
#print axioms LeanCrypto.Proofs.BabyJubjub.montgomery_add_construct
#print axioms LeanCrypto.Proofs.BabyJubjub.montgomery_double_construct
