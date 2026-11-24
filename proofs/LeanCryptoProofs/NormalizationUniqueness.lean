import LeanCryptoProofs.AssemblyFormula
import LeanCryptoProofs.NormalizedProofCodec

set_option autoImplicit false

namespace LeanCrypto.Proofs.Groth16Assembly

open LeanCrypto.BN254 LeanCrypto.Proofs.WindowedMSM

theorem g1_affinePoint_injective (left right : G1.Affine)
    (leftOn : left.onCurve = true) (rightOn : right.onCurve = true)
    (equal : LeanCrypto.Proofs.BN254Group.affinePoint left leftOn =
      LeanCrypto.Proofs.BN254Group.affinePoint right rightOn) : left = right := by
  have coordinates := WeierstrassCurve.Affine.Point.some.inj equal
  have x := LeanCrypto.Proofs.BN254Fp.model_injective coordinates.1
  have y := LeanCrypto.Proofs.BN254Fp.model_injective coordinates.2
  cases left
  cases right
  cases x
  cases y
  rfl

theorem g2_affinePoint_injective (left right : G2.Affine)
    (leftOn : left.onCurve = true) (rightOn : right.onCurve = true)
    (equal : LeanCrypto.Proofs.BN254G2Group.affinePoint left leftOn =
      LeanCrypto.Proofs.BN254G2Group.affinePoint right rightOn) : left = right := by
  have coordinates := WeierstrassCurve.Affine.Point.some.inj equal
  have x := LeanCrypto.Proofs.BN254Fp2.model_injective coordinates.1
  have y := LeanCrypto.Proofs.BN254Fp2.model_injective coordinates.2
  cases left
  cases right
  cases x
  cases y
  rfl

theorem g1_represents_unique (left right : Option G1.Affine)
    (point : LeanCrypto.Proofs.BN254Group.curve.toAffine.Point)
    (first : LeanCrypto.Proofs.BN254Group.Represents left point)
    (second : LeanCrypto.Proofs.BN254Group.Represents right point) : left = right := by
  cases left with
  | none =>
    cases right with
    | none => rfl
    | some right =>
      obtain ⟨onCurve, equal⟩ := second
      rw [show point = 0 from first] at equal
      cases equal
  | some left =>
    obtain ⟨leftOn, leftEqual⟩ := first
    cases right with
    | none =>
      rw [show point = 0 from second] at leftEqual
      cases leftEqual
    | some right =>
      obtain ⟨rightOn, rightEqual⟩ := second
      exact congrArg some (g1_affinePoint_injective left right leftOn rightOn
        (leftEqual.symm.trans rightEqual))

theorem g2_represents_unique (left right : Option G2.Affine)
    (point : LeanCrypto.Proofs.BN254G2Group.curve.toAffine.Point)
    (first : LeanCrypto.Proofs.BN254G2Group.Represents left point)
    (second : LeanCrypto.Proofs.BN254G2Group.Represents right point) : left = right := by
  cases left with
  | none =>
    cases right with
    | none => rfl
    | some right =>
      obtain ⟨onCurve, equal⟩ := second
      rw [show point = 0 from first] at equal
      cases equal
  | some left =>
    obtain ⟨leftOn, leftEqual⟩ := first
    cases right with
    | none =>
      rw [show point = 0 from second] at leftEqual
      cases leftEqual
    | some right =>
      obtain ⟨rightOn, rightEqual⟩ := second
      exact congrArg some (g2_affinePoint_injective left right leftOn rightOn
        (leftEqual.symm.trans rightEqual))

theorem g1_normalization_unique (left right : G1.Jacobian)
    (leftAdmitted : G1Admitted left) (rightAdmitted : G1Admitted right)
    (equal : g1 left = g1 right) : left.toAffine = right.toAffine := by
  obtain ⟨leftOut, leftBuilt, leftMeaning⟩ :=
    LeanCrypto.Proofs.BN254Group.toAffine_represents_groupPoint left leftAdmitted
  obtain ⟨rightOut, rightBuilt, rightMeaning⟩ :=
    LeanCrypto.Proofs.BN254Group.toAffine_represents_groupPoint right rightAdmitted
  have unique := g1_represents_unique leftOut rightOut (g1 right) (equal ▸ leftMeaning) rightMeaning
  rw [leftBuilt, rightBuilt, unique]

theorem g2_normalization_unique (left right : G2.Jacobian)
    (leftAdmitted : G2Admitted left) (rightAdmitted : G2Admitted right)
    (equal : g2 left = g2 right) : left.toAffine = right.toAffine := by
  obtain ⟨leftOut, leftBuilt, leftMeaning⟩ :=
    LeanCrypto.Proofs.BN254G2Group.toAffine_represents_groupPoint left leftAdmitted
  obtain ⟨rightOut, rightBuilt, rightMeaning⟩ :=
    LeanCrypto.Proofs.BN254G2Group.toAffine_represents_groupPoint right rightAdmitted
  have unique := g2_represents_unique leftOut rightOut (g2 right) (equal ▸ leftMeaning) rightMeaning
  rw [leftBuilt, rightBuilt, unique]

end LeanCrypto.Proofs.Groth16Assembly

#print axioms LeanCrypto.Proofs.Groth16Assembly.g1_affinePoint_injective
#print axioms LeanCrypto.Proofs.Groth16Assembly.g2_affinePoint_injective
#print axioms LeanCrypto.Proofs.Groth16Assembly.g1_represents_unique
#print axioms LeanCrypto.Proofs.Groth16Assembly.g2_represents_unique
#print axioms LeanCrypto.Proofs.Groth16Assembly.g1_normalization_unique
#print axioms LeanCrypto.Proofs.Groth16Assembly.g2_normalization_unique
