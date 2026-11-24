import LeanCryptoProofs.WindowedMSM.PublicG1

set_option autoImplicit false
namespace LeanCrypto.Proofs.WindowedMSM
open LeanCrypto.BN254.G1 LeanCrypto.Groth16.Types LeanCrypto.Proofs.BN254Jacobian

def decodedG1Value : DecodedG1 → Jacobian
  | .identity => Jacobian.infinity
  | .point point => Jacobian.ofAffine ⟨Fp.ofNat point.x, Fp.ofNat point.y⟩

def ValidG1 : DecodedG1 → Prop
  | .identity => True
  | .point point => point.x < basePrime ∧ point.y < basePrime ∧
      (⟨Fp.ofNat point.x, Fp.ofNat point.y⟩ : Affine).onCurve = true

theorem nativeG1Point_construct (input : DecodedG1) (valid : ValidG1 input) :
    nativeG1Point input = .ok (decodedG1Value input) := by
  cases input with
  | identity => rfl
  | point point =>
    obtain ⟨xBound, yBound, onCurve⟩ := valid
    change (do let checked ← Affine.checked point.x point.y
               pure (Jacobian.ofAffine checked)) = _
    simp [Affine.checked, Nat.not_le.mpr xBound, Nat.not_le.mpr yBound, onCurve,
      decodedG1Value, pure, Except.pure, bind, Except.bind]

theorem list_decodeG1_construct (inputs : List DecodedG1)
    (valid : ∀ input ∈ inputs, ValidG1 input) :
    inputs.mapM nativeG1Point = .ok (inputs.map decodedG1Value) := by
  induction inputs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapM_cons, nativeG1Point_construct head (valid head (by simp)),
      ih (fun input member => valid input (by simp [member]))]
    rfl

theorem decodeG1_construct (inputs : Array DecodedG1)
    (valid : ∀ input ∈ inputs, ValidG1 input) :
    inputs.mapM nativeG1Point = .ok (inputs.map decodedG1Value) := by
  rw [Array.mapM_eq_mapM_toList, list_decodeG1_construct inputs.toList
    (fun input member => valid input (Array.mem_def.mpr member))]
  simp [Functor.map, Except.map, ← List.map_toArray]

/-- Original valid points and scalar bounds construct the actual public MSM
result. No successful decoder, MSM, normalizer, or final check is assumed. -/
theorem msmG1_construct (points : Array DecodedG1) (scalars : Array Nat)
    (counts : points.size = scalars.size)
    (canonical : scalars.all (· < LeanCrypto.Groth16.MSM.order) = true)
    (valid : ∀ input ∈ points, ValidG1 input) :
    LeanCrypto.Groth16.MSM.msmG1 points scalars = .ok
      (nativeWindowed (points.map decodedG1Value) scalars Jacobian.infinity
        Jacobian.add Jacobian.double) := by
  rw [msmG1_source]
  simp [counts, canonical, decodeG1_construct points valid, Except.map]

theorem msmG1_construct_normalized_sum (points : Array DecodedG1) (scalars : Array Nat)
    (counts : points.size = scalars.size)
    (canonical : scalars.all (· < LeanCrypto.Groth16.MSM.order) = true)
    (valid : ∀ input ∈ points, ValidG1 input) :
    ∃ (result : Jacobian) (output : Option Affine),
      LeanCrypto.Groth16.MSM.msmG1 points scalars = .ok result ∧
      result.toAffine = .ok output ∧
      LeanCrypto.Proofs.BN254Group.Represents output
        (∑ index ∈ Finset.range points.size,
          (scalars[index]! % LeanCrypto.Groth16.MSM.order) •
            LeanCrypto.Proofs.BN254Group.groupPoint (points.map decodedG1Value)[index]!) := by
  have constructed := msmG1_construct points scalars counts canonical valid
  obtain ⟨decoded, output, source, _, normalized, represented⟩ :=
    msmG1_success_normalized_sum points scalars _ constructed
  have equal : decoded = points.map decodedG1Value :=
    Except.ok.inj (source.symm.trans (decodeG1_construct points valid))
  subst decoded
  exact ⟨_, output, constructed, normalized, represented⟩


end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.nativeG1Point_construct
#print axioms LeanCrypto.Proofs.WindowedMSM.list_decodeG1_construct
#print axioms LeanCrypto.Proofs.WindowedMSM.decodeG1_construct
#print axioms LeanCrypto.Proofs.WindowedMSM.msmG1_construct
#print axioms LeanCrypto.Proofs.WindowedMSM.msmG1_construct_normalized_sum
