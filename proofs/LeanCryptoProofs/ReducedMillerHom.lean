import LeanCryptoProofs.ReducedLineCocycle
import LeanCryptoProofs.MillerAlgebra

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate

def reducedLineUnit (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup) : BN254Fp12.Fieldˣ :=
  Units.mk0 (reducedLine evaluation onCurve first second)
    (pow_ne_zero _ (evaluatedLine_nonzero evaluation onCurve first second))

def reducedCocycle (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true) :
    MillerAlgebra.Cocycle twistSubgroup (Additive BN254Fp12.Fieldˣ) where
  value first second := Additive.ofMul (reducedLineUnit evaluation onCurve first second)
  zeroLeft point := by
    change reducedLineUnit evaluation onCurve 0 point = 1
    apply Units.val_injective
    exact reducedLine_zero_left evaluation onCurve point
  symmetric first second := by
    apply Units.val_injective
    exact reducedLine_symmetric evaluation onCurve first second
  associative first second third := by
    change reducedLineUnit evaluation onCurve first second * reducedLineUnit evaluation onCurve (first + second) third =
      reducedLineUnit evaluation onCurve second third * reducedLineUnit evaluation onCurve first (second + third)
    apply Units.val_injective
    simp only [Units.val_mul]
    exact (reducedLine_cocycle evaluation onCurve first second third).trans (mul_comm _ _)

theorem reducedCocycle_q_torsion (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup) :
    LeanCrypto.BN254.G1.scalarPrime • (reducedCocycle evaluation onCurve).value first second = 0 := by
  change reducedLineUnit evaluation onCurve first second ^ LeanCrypto.BN254.G1.scalarPrime = 1
  apply Units.val_injective
  exact reducedLine_q_order evaluation onCurve first second

theorem reduced_miller_add (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistSubgroup)
    (firstTorsion : LeanCrypto.BN254.G1.scalarPrime • first = 0)
    (secondTorsion : LeanCrypto.BN254.G1.scalarPrime • second = 0) :
    MillerAlgebra.miller (reducedCocycle evaluation onCurve) LeanCrypto.BN254.G1.scalarPrime (first + second) =
      MillerAlgebra.miller (reducedCocycle evaluation onCurve) LeanCrypto.BN254.G1.scalarPrime first +
      MillerAlgebra.miller (reducedCocycle evaluation onCurve) LeanCrypto.BN254.G1.scalarPrime second :=
  MillerAlgebra.miller_q_add _ _ first second firstTorsion secondTorsion
    (reducedCocycle_q_torsion evaluation onCurve first second)

def twistQTorsion : AddSubgroup twistSubgroup where
  carrier point := LeanCrypto.BN254.G1.scalarPrime • point = 0
  zero_mem' := by change LeanCrypto.BN254.G1.scalarPrime • (0 : twistSubgroup) = 0; exact nsmul_zero _
  add_mem' := by
    intro first second h1 h2
    change LeanCrypto.BN254.G1.scalarPrime • first = 0 at h1
    change LeanCrypto.BN254.G1.scalarPrime • second = 0 at h2
    change LeanCrypto.BN254.G1.scalarPrime • (first + second) = 0
    rw [nsmul_add, h1, h2, add_zero]
  neg_mem' := by
    intro point h
    change LeanCrypto.BN254.G1.scalarPrime • point = 0 at h
    change LeanCrypto.BN254.G1.scalarPrime • (-point) = 0
    rw [neg_nsmul, h, neg_zero]

def qReducedCocycle (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true) :
    MillerAlgebra.Cocycle twistQTorsion (Additive BN254Fp12.Fieldˣ) where
  value first second := (reducedCocycle evaluation onCurve).value first.val second.val
  zeroLeft point := (reducedCocycle evaluation onCurve).zeroLeft point.val
  symmetric first second := (reducedCocycle evaluation onCurve).symmetric first.val second.val
  associative first second third := (reducedCocycle evaluation onCurve).associative first.val second.val third.val

/-- A constructed homomorphism on the q-torsion twist subgroup. Its line
cocycle is derived from the mathematical curve function field and actual
final exponent; no bilinearity hypothesis is supplied. -/
def pairingSecondHom (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true) :
    twistQTorsion →+ Additive BN254Fp12.Fieldˣ :=
  MillerAlgebra.millerHom (qReducedCocycle evaluation onCurve) LeanCrypto.BN254.G1.scalarPrime
    (fun point => by apply Subtype.ext; exact point.property)
    (fun first second => reducedCocycle_q_torsion evaluation onCurve first.val second.val)

theorem pairingSecondHom_add (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (first second : twistQTorsion) :
    pairingSecondHom evaluation onCurve (first + second) =
      pairingSecondHom evaluation onCurve first + pairingSecondHom evaluation onCurve second :=
  (pairingSecondHom evaluation onCurve).map_add first second

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.reducedCocycle_q_torsion
#print axioms LeanCrypto.Proofs.BN254Tate.reduced_miller_add
#print axioms LeanCrypto.Proofs.BN254Tate.pairingSecondHom_add
