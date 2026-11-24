import LeanCryptoProofs.WindowedMSM.Transport
import LeanCryptoProofs.G2ScalarMulGroupLaw

set_option autoImplicit false

namespace LeanCrypto.Proofs.WindowedMSM

open LeanCrypto.BN254.G2 LeanCrypto.Proofs.BN254G2Jacobian LeanCrypto.Proofs.BN254G2Group

structure AdmittedG2 where
  point : Jacobian
  admitted : Admissible point

def AdmittedG2.zero : AdmittedG2 := ⟨Jacobian.infinity, infinity_admissible⟩
instance : Inhabited AdmittedG2 := ⟨AdmittedG2.zero⟩

def AdmittedG2.add (left right : AdmittedG2) : AdmittedG2 :=
  ⟨left.point.add right.point, add_admissible _ _ left.admitted right.admitted⟩

def AdmittedG2.double (point : AdmittedG2) : AdmittedG2 :=
  ⟨point.point.double, double_admissible _ point.admitted⟩

/-- The actual private native G2 window/bucket engine computes the true
group weighted sum for admitted input representatives and canonical scalars.
The public msmG2 decoder adapter is a separate source-provenance obligation. -/
theorem native_g2_windowed_sum (points : Array AdmittedG2) (scalars : Array Nat)
    (canonical : ∀ index, index < points.size → scalars[index]! < LeanCrypto.Groth16.MSM.order) :
    groupPoint (nativeWindowed (points.map AdmittedG2.point) scalars Jacobian.infinity
      Jacobian.add Jacobian.double) =
      ∑ index ∈ Finset.range points.size, scalars[index]! • groupPoint points[index]!.point := by
  have native := nativeWindowed_map AdmittedG2.point rfl
    AdmittedG2.add Jacobian.add AdmittedG2.double Jacobian.double
    (by intros; rfl) (by intros; rfl) points scalars AdmittedG2.zero
  dsimp only [AdmittedG2.zero] at native
  let project : AdmittedG2 → curve.toAffine.Point := fun point => groupPoint point.point
  have defaults : project default = default := infinity_groupPoint
  have mathematical := nativeWindowed_map project defaults
    AdmittedG2.add (· + ·) AdmittedG2.double (fun point => point + point)
    (fun left right => add_groupPoint _ _ left.admitted right.admitted)
    (fun point => double_groupPoint _ point.admitted) points scalars AdmittedG2.zero
  rw [← native]
  change project (nativeWindowed points scalars AdmittedG2.zero AdmittedG2.add AdmittedG2.double) = _
  rw [mathematical]
  have zero : project AdmittedG2.zero = 0 := infinity_groupPoint
  rw [zero, native_group_sum]
  · simp only [Array.size_map, map_getBang project defaults]
    rfl
  · intro index bounded
    exact canonical index (by simpa using bounded)

theorem native_g2_raw_windowed_sum (points : Array Jacobian) (scalars : Array Nat)
    (admitted : ∀ point ∈ points, Admissible point)
    (canonical : ∀ index, index < points.size → scalars[index]! < LeanCrypto.Groth16.MSM.order) :
    groupPoint (nativeWindowed points scalars Jacobian.infinity Jacobian.add Jacobian.double) =
      ∑ index ∈ Finset.range points.size, scalars[index]! • groupPoint points[index]! := by
  let packed : Array AdmittedG2 := points.pmap (fun point proof => ⟨point, proof⟩) admitted
  have forgotten : packed.map AdmittedG2.point = points := by
    simp [packed, Array.map_pmap, Array.pmap_eq_map]
  have shape := congrArg Array.size forgotten
  simp only [Array.size_map] at shape
  have result := native_g2_windowed_sum packed scalars (by
    intro index bounded
    exact canonical index (by simpa only [shape] using bounded))
  rw [forgotten, shape] at result
  rw [result]
  apply Finset.sum_congr rfl
  intro index member
  have value := map_getBang AdmittedG2.point rfl packed index
  rw [forgotten] at value
  rw [value]

theorem native_g2_raw_windowed_admissible (points : Array Jacobian) (scalars : Array Nat)
    (admitted : ∀ point ∈ points, Admissible point) :
    Admissible (nativeWindowed points scalars Jacobian.infinity Jacobian.add Jacobian.double) := by
  let packed : Array AdmittedG2 := points.pmap (fun point proof => ⟨point, proof⟩) admitted
  have forgotten : packed.map AdmittedG2.point = points := by
    simp [packed, Array.map_pmap, Array.pmap_eq_map]
  have native := nativeWindowed_map AdmittedG2.point rfl
    AdmittedG2.add Jacobian.add AdmittedG2.double Jacobian.double
    (by intros; rfl) (by intros; rfl) packed scalars AdmittedG2.zero
  dsimp only [AdmittedG2.zero] at native
  rw [forgotten] at native
  rw [← native]
  exact (nativeWindowed packed scalars AdmittedG2.zero AdmittedG2.add AdmittedG2.double).admitted

end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.native_g2_windowed_sum

#print axioms LeanCrypto.Proofs.WindowedMSM.native_g2_raw_windowed_sum

#print axioms LeanCrypto.Proofs.WindowedMSM.native_g2_raw_windowed_admissible
