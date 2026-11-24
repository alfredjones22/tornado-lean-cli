import LeanCryptoProofs.BilinearPairing
import LeanCryptoProofs.AssemblyQap

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open Groth16Assembly
local instance : NeZero LeanCrypto.BN254.G1.scalarPrime := ⟨by decide⟩

theorem scalarG2_q_torsion (value : Fr) : LeanCrypto.BN254.G1.scalarPrime • scalarG2 value = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

def scalarTwistHom : Fr →+ twistQTorsion where
  toFun value := ⟨embedTwistHom (scalarG2 value), by
    change LeanCrypto.BN254.G1.scalarPrime • embedTwistHom (scalarG2 value) = 0
    rw [← map_nsmul, scalarG2_q_torsion, map_zero]⟩
  map_zero' := by apply Subtype.ext; apply Subtype.ext; simp
  map_add' first second := by apply Subtype.ext; apply Subtype.ext; simp

def scalarPairHom : Fr →+ (Fr →+ Additive BN254Fp12.Fieldˣ) where
  toFun first := (pairingHom (scalarG1 first)).comp scalarTwistHom
  map_zero' := by apply AddMonoidHom.ext; intro second; simp
  map_add' first second := by
    apply AddMonoidHom.ext
    intro value
    change pairingHom (scalarG1 (first + second)) (scalarTwistHom value) = _
    rw [map_add, pairingHom_first_add]
    rfl

theorem scalarPair_product (first second : Fr) :
    scalarPairHom first second = scalarPairHom (first * second) 1 := by
  have secondEq : second = second.val • (1 : Fr) := by simp [nsmul_eq_mul]
  calc
    _ = scalarPairHom first (second.val • 1) := congrArg (scalarPairHom first) secondEq
    _ = second.val • scalarPairHom first 1 := (scalarPairHom first).map_nsmul 1 second.val
    _ = scalarPairHom (second.val • first) 1 := by
      exact (congrArg (fun hom : Fr →+ Additive BN254Fp12.Fieldˣ => hom 1)
        (scalarPairHom.map_nsmul first second.val)).symm
    _ = _ := by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

theorem scalar_verifier_equation (a b c alpha beta gamma delta publicIC : Fr)
    (equation : a * b = alpha * beta + publicIC * gamma + c * delta) :
    scalarPairHom (-a) b + scalarPairHom alpha beta +
      scalarPairHom publicIC gamma + scalarPairHom c delta = 0 := by
  rw [scalarPair_product (-a) b, scalarPair_product alpha beta, scalarPair_product publicIC gamma,
    scalarPair_product c delta]
  have zero : -a * b + alpha * beta + publicIC * gamma + c * delta = 0 := by linear_combination -equation
  calc
    _ = scalarPairHom (-a * b + alpha * beta + publicIC * gamma + c * delta) 1 := by
      simp only [map_add, AddMonoidHom.add_apply]
    _ = 0 := by rw [zero, map_zero]; rfl

theorem nativeTwistTorsion_scalar (point : LeanCrypto.BN254.G2.Affine) (onCurve : point.onCurve = true)
    (value : Fr) (span : BN254G2Group.affinePoint point onCurve = scalarG2 value)
    (torsion : LeanCrypto.BN254.G1.scalarPrime • BN254G2Group.affinePoint point onCurve = 0) :
    nativeTwistTorsion point onCurve torsion = scalarTwistHom value := by
  apply Subtype.ext
  change embedTwistHom (BN254G2Group.affinePoint point onCurve) = embedTwistHom (scalarG2 value)
  rw [span]

theorem pairingHom_scalar_span (first : BN254Group.curve.toAffine.Point) (second : twistQTorsion)
    (a b : Fr) (firstSpan : first = scalarG1 a) (secondSpan : second = scalarTwistHom b) :
    pairingHom first second = scalarPairHom a b := by
  rw [firstSpan, secondSpan]
  rfl

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.scalarG2_q_torsion
#print axioms LeanCrypto.Proofs.BN254Tate.scalarPair_product
#print axioms LeanCrypto.Proofs.BN254Tate.scalar_verifier_equation
#print axioms LeanCrypto.Proofs.BN254Tate.nativeTwistTorsion_scalar
#print axioms LeanCrypto.Proofs.BN254Tate.pairingHom_scalar_span
