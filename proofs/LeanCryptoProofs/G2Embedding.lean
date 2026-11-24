import LeanCryptoProofs.NativeLineGraph
import LeanCryptoProofs.MillerInputConstruction
import LeanCryptoProofs.ReducedMillerHom
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 LeanCrypto.BN254.TatePairing

def nativeG2Affine (x y : BN254Fp2.Field) : Affine := ⟨BN254Fp2.encode x, BN254Fp2.encode y⟩

theorem nativeG2Affine_onCurve (x y : BN254Fp2.Field) (equation : BN254G2Group.curve.toAffine.Equation x y) :
    (nativeG2Affine x y).onCurve = true := by
  apply (BN254Fp2.affine_onCurve_iff _).2
  simp only [nativeG2Affine, BN254Fp2.model_encode]
  simpa [WeierstrassCurve.Affine.equation_iff, BN254G2Group.curve] using equation

def embedGroup : BN254G2Group.curve.toAffine.Point → curve12.toAffine.Point
  | .zero => 0
  | .some x y nonsingular =>
    modelPoint (embedG2 (nativeG2Affine x y))
      (embedG2_onCurve _ (nativeG2Affine_onCurve x y nonsingular.left))

theorem embedGroup_native (point : Affine) (onCurve : point.onCurve = true) :
    embedGroup (BN254G2Group.affinePoint point onCurve) =
      modelPoint (embedG2 point) (embedG2_onCurve point onCurve) := by
  cases point
  simp only [BN254G2Group.affinePoint, embedGroup, nativeG2Affine, BN254Fp2.encode_model]

theorem embedGroup_represents (result : Option Affine) (meaning : BN254G2Group.curve.toAffine.Point)
    (represented : BN254G2Group.Represents result meaning) :
    Represents12 (result.map embedG2) (embedGroup meaning) := by
  cases result with
  | none => rw [represented]; rfl
  | some point =>
    obtain ⟨onCurve, equal⟩ := represented
    rw [equal]
    exact ⟨embedG2_onCurve point onCurve, embedGroup_native point onCurve⟩

theorem represents12_unique (result : Option Point) (first second : curve12.toAffine.Point)
    (firstRep : Represents12 result first) (secondRep : Represents12 result second) : first = second := by
  cases result with
  | none => exact firstRep.trans secondRep.symm
  | some point =>
    obtain ⟨firstCurve, firstEq⟩ := firstRep
    obtain ⟨secondCurve, secondEq⟩ := secondRep
    exact firstEq.trans secondEq.symm

theorem embedGroup_add (first second : BN254G2Group.curve.toAffine.Point) :
    embedGroup (first + second) = embedGroup first + embedGroup second := by
  cases first with
  | zero => rfl
  | some x1 y1 h1 =>
    cases second with
    | zero => rfl
    | some x2 y2 h2 =>
      let r := nativeG2Affine x1 y1
      let s := nativeG2Affine x2 y2
      have rCurve : r.onCurve = true := nativeG2Affine_onCurve x1 y1 h1.left
      have sCurve : s.onCurve = true := nativeG2Affine_onCurve x2 y2 h2.left
      have rMeaning : BN254G2Group.affinePoint r rCurve = .some x1 y1 h1 := by
        simp only [BN254G2Group.affinePoint, r, nativeG2Affine, BN254Fp2.model_encode]
      have sMeaning : BN254G2Group.affinePoint s sCurve = .some x2 y2 h2 := by
        simp only [BN254G2Group.affinePoint, s, nativeG2Affine, BN254Fp2.model_encode]
      have evaluationCurve : LeanCrypto.BN254.G1.generator.onCurve = true := by decide +kernel
      obtain ⟨factor, sum, native, groupRep⟩ := twist_line_construct r s rCurve sCurve
        LeanCrypto.BN254.G1.generator evaluationCurve
      rw [rMeaning, sMeaning] at groupRep
      obtain ⟨factor12, sum12, actual, curveRep, _⟩ := nativeLine_graph (embedG2 r) (embedG2 s)
        (embedG2_onCurve r rCurve) (embedG2_onCurve s sCurve)
        (native_embed_twist r rCurve) (native_embed_twist s sCurve)
        LeanCrypto.BN254.G1.generator evaluationCurve
      have outputs := Except.ok.inj (native.symm.trans actual)
      have sameSum : sum.map embedG2 = sum12 := congrArg Prod.snd outputs
      have transported := embedGroup_represents sum _ groupRep
      rw [sameSum] at transported
      have mappedR : modelPoint (embedG2 r) (embedG2_onCurve r rCurve) = embedGroup (.some x1 y1 h1) := by
        rw [← rMeaning, embedGroup_native]
      have mappedS : modelPoint (embedG2 s) (embedG2_onCurve s sCurve) = embedGroup (.some x2 y2 h2) := by
        rw [← sMeaning, embedGroup_native]
      rw [mappedR, mappedS] at curveRep
      exact represents12_unique sum12 _ _ transported curveRep

def embedGroupHom : BN254G2Group.curve.toAffine.Point →+ curve12.toAffine.Point where
  toFun := embedGroup
  map_zero' := rfl
  map_add' := embedGroup_add

theorem embedGroup_zero_iff (point : BN254G2Group.curve.toAffine.Point) : embedGroup point = 0 ↔ point = 0 := by
  cases point with
  | zero => constructor <;> intro _ <;> rfl
  | some x y nonsingular =>
    constructor
    · intro impossible
      unfold embedGroup modelPoint at impossible
      cases impossible
    · intro impossible
      cases impossible

theorem embedGroupHom_injective : Function.Injective embedGroupHom := by
  intro first second equal
  have difference : embedGroup (first - second) = 0 := by
    change embedGroupHom (first - second) = 0
    rw [map_sub, equal, sub_self]
  exact sub_eq_zero.mp ((embedGroup_zero_iff _).1 difference)

theorem native_embed_groupPoint (point : Affine) (onCurve : point.onCurve = true) :
    embedGroupHom (BN254G2Group.groupPoint (Jacobian.ofAffine point)) =
      modelPoint (embedG2 point) (embedG2_onCurve point onCurve) := by
  rw [ofAffine_groupPoint point onCurve]
  exact embedGroup_native point onCurve

theorem embedGroup_isTwist (point : BN254G2Group.curve.toAffine.Point) :
    IsTwistPoint (embedGroup point) := by
  cases point with
  | zero => trivial
  | some x y nonsingular => exact native_embed_twist _ (nativeG2Affine_onCurve x y nonsingular.left)

def embedTwistHom : BN254G2Group.curve.toAffine.Point →+ twistSubgroup where
  toFun point := ⟨embedGroup point, embedGroup_isTwist point⟩
  map_zero' := rfl
  map_add' first second := Subtype.ext (embedGroup_add first second)

def nativeTwistTorsion (point : Affine) (onCurve : point.onCurve = true)
    (torsion : LeanCrypto.BN254.G1.scalarPrime • BN254G2Group.affinePoint point onCurve = 0) :
    twistQTorsion :=
  ⟨embedTwistHom (BN254G2Group.affinePoint point onCurve), by
    change LeanCrypto.BN254.G1.scalarPrime • embedTwistHom (BN254G2Group.affinePoint point onCurve) = 0
    rw [← map_nsmul, torsion, map_zero]⟩

theorem nativeTwistTorsion_point (point : Affine) (onCurve : point.onCurve = true)
    (torsion : LeanCrypto.BN254.G1.scalarPrime • BN254G2Group.affinePoint point onCurve = 0) :
    (nativeTwistTorsion point onCurve torsion).val.val =
      modelPoint (embedG2 point) (embedG2_onCurve point onCurve) :=
  embedGroup_native point onCurve

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.nativeG2Affine_onCurve
#print axioms LeanCrypto.Proofs.BN254Tate.embedGroup_native
#print axioms LeanCrypto.Proofs.BN254Tate.embedGroup_represents
#print axioms LeanCrypto.Proofs.BN254Tate.represents12_unique
#print axioms LeanCrypto.Proofs.BN254Tate.embedGroup_add
#print axioms LeanCrypto.Proofs.BN254Tate.embedGroup_zero_iff
#print axioms LeanCrypto.Proofs.BN254Tate.embedGroupHom_injective
#print axioms LeanCrypto.Proofs.BN254Tate.native_embed_groupPoint
#print axioms LeanCrypto.Proofs.BN254Tate.embedGroup_isTwist
#print axioms LeanCrypto.Proofs.BN254Tate.nativeTwistTorsion_point
