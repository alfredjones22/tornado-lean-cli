import LeanCryptoProofs.BabyJubjub.NativeExtended

set_option autoImplicit false
namespace LeanCrypto.Proofs.BabyJubjub
open LeanCrypto.Proofs.BN254Fr LeanCrypto.Proofs.BabyJubjubField

theorem native_mul_canonical (x y : Nat) : nativeMul x y=(model x*model y).val := by
  apply canonical_injective (Nat.mod_lt _ (by decide)) (ZMod.val_lt _)
  change model (nativeMul x y)=model (model x*model y).val
  rw [native_mul_model,model_val]

theorem native_affine_body (p : RawPoint) : nativeAffine p = (do
      let invZ ← nativeInverse (rawZ p)
      let x := nativeMul (rawX p) invZ
      let y := nativeMul (rawY p) invZ
      let x2 := nativeMul x x
      let y2 := nativeMul y y
      if nativeAdd (nativeMul 168700 x2) y2 != nativeAdd 1 (nativeMul 168696 (nativeMul x2 y2)) then none
      else some (x,y)) := rfl

theorem native_affine_construct (p : RawPoint) (admitted : Admissible p) :
    nativeAffine p=some ((normalizedX p).val,(normalizedY p).val) := by
  have inverse := native_inverse_construct (rawZ p) admitted.1
  have xValue : nativeMul (rawX p) ((model (rawZ p))⁻¹).val=(normalizedX p).val := by
    rw [native_mul_canonical,model_val]
    rfl
  have yValue : nativeMul (rawY p) ((model (rawZ p))⁻¹).val=(normalizedY p).val := by
    rw [native_mul_canonical,model_val]
    rfl
  rw [native_affine_body,inverse]
  simp only [bind,Option.bind]
  rw [xValue,yValue]
  have equation :
      nativeAdd (nativeMul 168700 (nativeMul (normalizedX p).val (normalizedX p).val))
        (nativeMul (normalizedY p).val (normalizedY p).val)=
      nativeAdd 1 (nativeMul 168696 (nativeMul
        (nativeMul (normalizedX p).val (normalizedX p).val)
        (nativeMul (normalizedY p).val (normalizedY p).val))) := by
    apply canonical_injective (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    change model (nativeAdd _ _)=model (nativeAdd _ _)
    simp only [native_add_model,native_mul_model,model_val]
    have curve := normalized_curve p admitted
    simpa only [Edwards,pow_two,show model 168700=(168700:Field) from rfl,
      show model 168696=(168696:Field) from rfl,show model 1=(1:Field) from rfl,mul_assoc] using curve
  simp only [equation,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]

end LeanCrypto.Proofs.BabyJubjub
#print axioms LeanCrypto.Proofs.BabyJubjub.native_mul_canonical
#print axioms LeanCrypto.Proofs.BabyJubjub.native_affine_body
#print axioms LeanCrypto.Proofs.BabyJubjub.native_affine_construct
