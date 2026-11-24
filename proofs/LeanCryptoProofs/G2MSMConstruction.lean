import LeanCryptoProofs.G2PublicWindowedMSM

set_option autoImplicit false
namespace LeanCrypto.Proofs.WindowedMSM
open LeanCrypto.BN254.G2 LeanCrypto.Groth16.Types LeanCrypto.Proofs.BN254G2Jacobian

def decodedG2Value : DecodedG2 → Jacobian
  | .identity => Jacobian.infinity
  | .point point => Jacobian.ofAffine point

def ValidG2 : DecodedG2 → Prop
  | .identity => True
  | .point point => point.onCurve = true

theorem nativeG2Point_construct (input : DecodedG2) (valid : ValidG2 input) :
    nativeG2Point input = .ok (decodedG2Value input) := by
  cases input with
  | identity => rfl
  | point point =>
    change (if point.onCurve then Except.ok (Jacobian.ofAffine point)
      else Except.error "Groth16 G2 point is not on the twist.") = _
    rw [show point.onCurve = true from valid]
    rfl

theorem list_decodeG2_construct (inputs : List DecodedG2)
    (valid : ∀ input ∈ inputs, ValidG2 input) :
    inputs.mapM nativeG2Point = .ok (inputs.map decodedG2Value) := by
  induction inputs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.mapM_cons, nativeG2Point_construct head (valid head (by simp)),
      ih (fun input member => valid input (by simp [member]))]
    rfl

theorem decodeG2_construct (inputs : Array DecodedG2)
    (valid : ∀ input ∈ inputs, ValidG2 input) :
    inputs.mapM nativeG2Point = .ok (inputs.map decodedG2Value) := by
  rw [Array.mapM_eq_mapM_toList, list_decodeG2_construct inputs.toList
    (fun input member => valid input (Array.mem_def.mpr member))]
  simp [Functor.map, Except.map, ← List.map_toArray]

/-- Original valid points and scalar bounds construct the actual public MSM
result. No successful decoder, MSM, normalizer, or final check is assumed. -/
theorem msmG2_construct (points : Array DecodedG2) (scalars : Array Nat)
    (counts : points.size = scalars.size)
    (canonical : scalars.all (· < LeanCrypto.Groth16.MSM.order) = true)
    (valid : ∀ input ∈ points, ValidG2 input) :
    LeanCrypto.Groth16.MSM.msmG2 points scalars = .ok
      (nativeWindowed (points.map decodedG2Value) scalars Jacobian.infinity
        Jacobian.add Jacobian.double) := by
  rw [msmG2_source]
  simp [counts, canonical, decodeG2_construct points valid, Except.map]

theorem msmG2_construct_normalized_sum (points : Array DecodedG2) (scalars : Array Nat)
    (counts : points.size = scalars.size)
    (canonical : scalars.all (· < LeanCrypto.Groth16.MSM.order) = true)
    (valid : ∀ input ∈ points, ValidG2 input) :
    ∃ (result : Jacobian) (output : Option Affine),
      LeanCrypto.Groth16.MSM.msmG2 points scalars = .ok result ∧
      result.toAffine = .ok output ∧
      LeanCrypto.Proofs.BN254G2Group.Represents output
        (∑ index ∈ Finset.range points.size,
          (scalars[index]! % LeanCrypto.Groth16.MSM.order) •
            LeanCrypto.Proofs.BN254G2Group.groupPoint (points.map decodedG2Value)[index]!) := by
  have constructed := msmG2_construct points scalars counts canonical valid
  obtain ⟨decoded, output, source, _, normalized, represented⟩ :=
    msmG2_success_normalized_sum points scalars _ constructed
  have equal : decoded = points.map decodedG2Value :=
    Except.ok.inj (source.symm.trans (decodeG2_construct points valid))
  subst decoded
  exact ⟨_, output, constructed, normalized, represented⟩


end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.nativeG2Point_construct
#print axioms LeanCrypto.Proofs.WindowedMSM.list_decodeG2_construct
#print axioms LeanCrypto.Proofs.WindowedMSM.decodeG2_construct
#print axioms LeanCrypto.Proofs.WindowedMSM.msmG2_construct
#print axioms LeanCrypto.Proofs.WindowedMSM.msmG2_construct_normalized_sum
