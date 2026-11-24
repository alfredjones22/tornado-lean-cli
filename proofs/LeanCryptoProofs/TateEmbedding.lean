import LeanCryptoProofs.TateFieldBridge
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G1 LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField
open LeanCrypto.BN254.TatePairing

def fp2Hom : BN254Fp2.Field →+* BN254Fp12.Field :=
  (algebraMap BN254Fp6.Field BN254Fp12.Field).comp
    (algebraMap BN254Fp2.Field BN254Fp6.Field)

def fpHom : ZMod BN254Fp.P →+* BN254Fp12.Field :=
  fp2Hom.comp (algebraMap (ZMod BN254Fp.P) BN254Fp2.Field)

theorem model_embedFp2 (value : Fp2) :
    BN254Fp12.model (embedFp2 value) = fp2Hom (BN254Fp2.model value) := by
  apply QuadraticAlgebra.ext
  · simp [BN254Fp12.model, embedFp2, fp2Hom, BN254Fp6.model_formula]
  · simp [BN254Fp12.model, embedFp2, fp2Hom]

theorem model_embedFp (value : Fp) :
    BN254Fp12.model (embedFp value) = fpHom (BN254Fp.model value) := by
  change BN254Fp12.model (embedFp2 ⟨value, Fp.zero⟩) = _
  rw [model_embedFp2]
  apply congrArg fp2Hom
  apply QuadraticAlgebra.ext <;> simp [BN254Fp2.model]

theorem model_embed_nat (value : Nat) :
    BN254Fp12.model (embedFp (Fp.ofNat value)) = (value : BN254Fp12.Field) := by
  rw [model_embedFp, BN254Fp.model_ofNat, map_natCast]

theorem native_onCurve_iff (point : Point) : point.onCurve = true ↔
    BN254Fp12.model point.y ^ 2 = BN254Fp12.model point.x ^ 3 + 3 := by
  rw [Point.onCurve, BN254Fp12.model_beq]
  simp only [BN254Fp12.model_square, BN254Fp12.model_add, BN254Fp12.model_mul,
    model_embed_nat]
  simp only [← pow_succ, Nat.cast_ofNat]

theorem embedG1_onCurve (point : LeanCrypto.BN254.G1.Affine) (admitted : point.onCurve = true) :
    (embedG1 point).onCurve = true := by
  apply (native_onCurve_iff _).2
  change BN254Fp12.model (embedFp point.y) ^ 2 =
    BN254Fp12.model (embedFp point.x) ^ 3 + 3
  rw [model_embedFp, model_embedFp]
  have equation := congrArg fpHom ((BN254Fp.affine_onCurve_iff point).1 admitted)
  simpa only [map_pow, map_add, map_ofNat] using equation

theorem twist_coefficient : BN254Fp2.model twistB * BN254Fp6.xi = 3 := by decide +kernel

theorem model_embedG2_x (point : LeanCrypto.BN254.G2.Affine) :
    BN254Fp12.model (embedG2 point).x =
      ⟨algebraMap BN254Fp2.Field BN254Fp6.Field (BN254Fp2.model point.x) *
        AdjoinRoot.root BN254Fp6.cubic, 0⟩ := by
  apply QuadraticAlgebra.ext <;>
    simp [BN254Fp12.model, embedG2, BN254Fp6.model_formula, Fp6.zero]

theorem model_embedG2_y (point : LeanCrypto.BN254.G2.Affine) :
    BN254Fp12.model (embedG2 point).y =
      ⟨0, algebraMap BN254Fp2.Field BN254Fp6.Field (BN254Fp2.model point.y) *
        AdjoinRoot.root BN254Fp6.cubic⟩ := by
  apply QuadraticAlgebra.ext <;>
    simp [BN254Fp12.model, embedG2, BN254Fp6.model_formula, Fp6.zero]

theorem embedG2_onCurve (point : LeanCrypto.BN254.G2.Affine) (admitted : point.onCurve = true) :
    (embedG2 point).onCurve = true := by
  apply (native_onCurve_iff _).2
  rw [model_embedG2_x, model_embedG2_y]
  have equation := congrArg (AdjoinRoot.of BN254Fp6.cubic)
    ((BN254Fp2.affine_onCurve_iff point).1 admitted)
  simp only [map_pow, map_add] at equation
  have coefficient := congrArg (AdjoinRoot.of BN254Fp6.cubic) twist_coefficient
  simp only [map_mul, map_ofNat] at coefficient
  apply QuadraticAlgebra.ext
  · simp [pow_succ, BN254Fp6.model_v]
    ring_nf
    rw [BN254Fp6.root_cube]
    change (AdjoinRoot.of BN254Fp6.cubic) BN254Fp6.xi *
      (AdjoinRoot.of BN254Fp6.cubic) (BN254Fp2.model point.y) ^ 2 =
        (AdjoinRoot.of BN254Fp6.cubic) BN254Fp6.xi *
          (AdjoinRoot.of BN254Fp6.cubic) (BN254Fp2.model point.x) ^ 3 + 3
    rw [equation]
    linear_combination coefficient
  · simp [pow_succ]
    rfl

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.model_embedFp2
#print axioms LeanCrypto.Proofs.BN254Tate.model_embedFp
#print axioms LeanCrypto.Proofs.BN254Tate.model_embed_nat
#print axioms LeanCrypto.Proofs.BN254Tate.native_onCurve_iff
#print axioms LeanCrypto.Proofs.BN254Tate.embedG1_onCurve
#print axioms LeanCrypto.Proofs.BN254Tate.twist_coefficient
#print axioms LeanCrypto.Proofs.BN254Tate.model_embedG2_x
#print axioms LeanCrypto.Proofs.BN254Tate.model_embedG2_y
#print axioms LeanCrypto.Proofs.BN254Tate.embedG2_onCurve
