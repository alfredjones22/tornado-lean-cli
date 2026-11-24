import LeanCryptoProofs.BabyJubjub.Montgomery
import LeanCryptoProofs.BabyJubjub.NativeField

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BN254Fr LeanCrypto.Proofs.BabyJubjubField

abbrev RawPoint : Type := pedersenFieldPrivate LeanCrypto.ExtendedPoint
abbrev rawX (p : RawPoint) : Nat := (pedersenFieldPrivate LeanCrypto.ExtendedPoint.x) p
abbrev rawY (p : RawPoint) : Nat := (pedersenFieldPrivate LeanCrypto.ExtendedPoint.y) p
abbrev rawZ (p : RawPoint) : Nat := (pedersenFieldPrivate LeanCrypto.ExtendedPoint.z) p
abbrev rawT (p : RawPoint) : Nat := (pedersenFieldPrivate LeanCrypto.ExtendedPoint.t) p
abbrev nativeIdentity : RawPoint := pedersenFieldPrivate LeanCrypto.identity
abbrev nativeAddPoints (p q : RawPoint) : RawPoint := (pedersenFieldPrivate LeanCrypto.addPoints) p q
abbrev nativeScalarLoop (p : RawPoint) (n : Nat) (accumulator : RawPoint) : RawPoint :=
  (pedersenFieldPrivate LeanCrypto.scalarMulLoop) p n accumulator
abbrev nativeScalarMul (p : RawPoint) (n : Nat) : RawPoint := (pedersenFieldPrivate LeanCrypto.scalarMul) p n
abbrev nativeAffine (p : RawPoint) : Option (Nat × Nat) := (pedersenFieldPrivate LeanCrypto.affine) p

def X (p : RawPoint) : Field := model (rawX p)
def Y (p : RawPoint) : Field := model (rawY p)
def Z (p : RawPoint) : Field := model (rawZ p)
def T (p : RawPoint) : Field := model (rawT p)

def Admissible (p : RawPoint) : Prop :=
  Z p ≠ 0 ∧ T p*Z p=X p*Y p ∧
    168700*(X p)^2+(Y p)^2=(Z p)^2+168696*(T p)^2
  deriving Decidable

def normalizedX (p : RawPoint) : Field := X p / Z p
def normalizedY (p : RawPoint) : Field := Y p / Z p

def addE (p q : RawPoint) : Field := X p*Y q+Y p*X q
def addF (p q : RawPoint) : Field := Z p*Z q-168696*T p*T q
def addG (p q : RawPoint) : Field := Z p*Z q+168696*T p*T q
def addH (p q : RawPoint) : Field := Y p*Y q-168700*X p*X q

theorem native_add_coordinates (p q : RawPoint) :
    X (nativeAddPoints p q)=addE p q*addF p q ∧
    Y (nativeAddPoints p q)=addG p q*addH p q ∧
    Z (nativeAddPoints p q)=addF p q*addG p q ∧
    T (nativeAddPoints p q)=addE p q*addH p q := by
  change model (nativeMul _ _) = _ ∧ model (nativeMul _ _) = _ ∧
    model (nativeMul _ _) = _ ∧ model (nativeMul _ _) = _
  simp only [native_mul_model,native_add_model,native_sub_model]
  simp only [show (pedersenFieldPrivate LeanCrypto.curveA)=168700 from rfl,
    show (pedersenFieldPrivate LeanCrypto.curveD)=168696 from rfl]
  norm_num only [model,Nat.cast_ofNat]
  dsimp only [addE,addF,addG,addH,X,Y,Z,T,rawX,rawY,rawZ,rawT,model]
  refine ⟨?_,?_,?_,?_⟩ <;> ring

theorem identity_admissible : Admissible nativeIdentity := by
  decide +kernel

theorem normalized_curve (p : RawPoint) (admitted : Admissible p) :
    Edwards (normalizedX p) (normalizedY p) := by
  rcases admitted with ⟨nonzero,relation,equation⟩
  have product : T p = X p*Y p/Z p := (eq_div_iff nonzero).2 relation
  rw [product] at equation
  unfold Edwards normalizedX normalizedY
  field_simp [nonzero] at equation ⊢
  linear_combination equation

theorem generator_admissible (p : RawPoint)
    (admitted : LeanCrypto.Pedersen.GeneratorAdmitted p) : Admissible p := by
  rcases admitted with ⟨xb,yb,zb,tb,nonzero,relation,equation⟩
  change rawZ p < Q at zb
  change rawZ p ≠ 0 at nonzero
  have zNonzero : model (rawZ p) ≠ 0 := by
    intro zero
    have reduced := (model_zero_iff (rawZ p)).1 zero
    rw [Nat.mod_eq_of_lt zb] at reduced
    exact nonzero reduced
  refine ⟨zNonzero,?_,?_⟩
  · change nativeMul (rawT p) (rawZ p)=nativeMul (rawX p) (rawY p) at relation
    have represented := congrArg model relation
    simpa only [native_mul_model,X,Y,Z,T] using represented
  · have represented := congrArg model equation
    change model (nativeAdd (nativeMul 168700 (nativeMul (rawX p) (rawX p))) (nativeMul (rawY p) (rawY p)))=
      model (nativeAdd (nativeMul (rawZ p) (rawZ p)) (nativeMul 168696 (nativeMul (rawT p) (rawT p)))) at represented
    simp only [native_add_model,native_mul_model] at represented
    simpa only [X,Y,Z,T,pow_two,show model 168700=(168700:Field) from rfl,
      show model 168696=(168696:Field) from rfl] using represented

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.native_add_coordinates
#print axioms LeanCrypto.Proofs.BabyJubjub.identity_admissible
#print axioms LeanCrypto.Proofs.BabyJubjub.normalized_curve
#print axioms LeanCrypto.Proofs.BabyJubjub.generator_admissible
