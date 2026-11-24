import LeanCryptoProofs.FirstArgumentHom

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate

def secondPairingHom (evaluation : BN254Group.curve.toAffine.Point) : twistQTorsion →+ Additive BN254Fp12.Fieldˣ :=
  match evaluation with
  | .zero => 0
  | .some x y h => pairingSecondHom (nativeG1Affine x y) (nativeG1Affine_onCurve x y h.left)

theorem secondPairingHom_apply (evaluation : BN254Group.curve.toAffine.Point) (point : twistQTorsion) :
    secondPairingHom evaluation point = firstValue evaluation point := by
  cases evaluation <;> rfl

def pairingHom : BN254Group.curve.toAffine.Point →+ (twistQTorsion →+ Additive BN254Fp12.Fieldˣ) where
  toFun := secondPairingHom
  map_zero' := rfl
  map_add' first second := by
    apply AddMonoidHom.ext
    intro point
    change secondPairingHom (first + second) point = secondPairingHom first point + secondPairingHom second point
    rw [secondPairingHom_apply, secondPairingHom_apply, secondPairingHom_apply]
    exact firstValue_add first second point

theorem pairingHom_first_add (first second : BN254Group.curve.toAffine.Point) (point : twistQTorsion) :
    pairingHom (first + second) point = pairingHom first point + pairingHom second point := by
  exact congrArg (fun hom : twistQTorsion →+ Additive BN254Fp12.Fieldˣ => hom point) (pairingHom.map_add first second)

theorem pairingHom_second_add (evaluation : BN254Group.curve.toAffine.Point) (first second : twistQTorsion) :
    pairingHom evaluation (first + second) = pairingHom evaluation first + pairingHom evaluation second :=
  (pairingHom evaluation).map_add first second

theorem pairingHom_native_first (evaluation : LeanCrypto.BN254.G1.Affine) (onCurve : evaluation.onCurve = true)
    (point : twistQTorsion) :
    pairingHom (BN254Group.affinePoint evaluation onCurve) point = pairingSecondHom evaluation onCurve point := by
  cases evaluation
  simp only [BN254Group.affinePoint, pairingHom, secondPairingHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    nativeG1Affine, BN254Fp.encode_model]

/-- Both argument laws are derived from the independent curve function field,
native tower model and full Miller source graph. This constructs the exact
public native output on the original finite valid inputs. -/
theorem pair_construct_bilinear (evaluation : LeanCrypto.BN254.G1.Affine) (point : LeanCrypto.BN254.G2.Affine)
    (evaluationCurve : evaluation.onCurve = true) (pointCurve : point.onCurve = true)
    (torsion : LeanCrypto.BN254.G1.scalarPrime • BN254G2Group.affinePoint point pointCurve = 0) :
    ∃ result : LeanCrypto.BN254.PairingField.Fp12, LeanCrypto.BN254.TatePairing.pair evaluation point = .ok result ∧
      BN254Fp12.model result =
        ((pairingHom (BN254Group.affinePoint evaluation evaluationCurve)
          (nativeTwistTorsion point pointCurve torsion)).toMul : BN254Fp12.Field) := by
  rw [pairingHom_native_first]
  exact pair_construct_second_hom evaluation point evaluationCurve pointCurve torsion

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.secondPairingHom_apply
#print axioms LeanCrypto.Proofs.BN254Tate.pairingHom_first_add
#print axioms LeanCrypto.Proofs.BN254Tate.pairingHom_second_add
#print axioms LeanCrypto.Proofs.BN254Tate.pairingHom_native_first
#print axioms LeanCrypto.Proofs.BN254Tate.pair_construct_bilinear
