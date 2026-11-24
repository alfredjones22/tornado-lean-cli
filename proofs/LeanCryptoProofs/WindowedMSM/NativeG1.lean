import LeanCryptoProofs.WindowedMSM.Transport

set_option autoImplicit false

namespace LeanCrypto.Proofs.WindowedMSM

open LeanCrypto.BN254.G1 LeanCrypto.Proofs.BN254Jacobian LeanCrypto.Proofs.BN254Group

structure AdmittedG1 where
  point : Jacobian
  admitted : Admissible point

def AdmittedG1.zero : AdmittedG1 := ⟨Jacobian.infinity, infinity_admissible⟩
instance : Inhabited AdmittedG1 := ⟨AdmittedG1.zero⟩

def AdmittedG1.add (left right : AdmittedG1) : AdmittedG1 :=
  ⟨left.point.add right.point, add_preserves_curve_certified _ _ left.admitted right.admitted⟩

def AdmittedG1.double (point : AdmittedG1) : AdmittedG1 :=
  ⟨point.point.double, double_preserves_curve_certified _ point.admitted⟩

/-- The actual private native G1 window/bucket engine computes the true
group weighted sum for admitted input representatives and canonical scalars.
The public msmG1 decoder adapter is a separate source-provenance obligation. -/
theorem native_g1_windowed_sum (points : Array AdmittedG1) (scalars : Array Nat)
    (canonical : ∀ index, index < points.size → scalars[index]! < LeanCrypto.Groth16.MSM.order) :
    groupPoint (nativeWindowed (points.map AdmittedG1.point) scalars Jacobian.infinity
      Jacobian.add Jacobian.double) =
      ∑ index ∈ Finset.range points.size, scalars[index]! • groupPoint points[index]!.point := by
  have native := nativeWindowed_map AdmittedG1.point rfl
    AdmittedG1.add Jacobian.add AdmittedG1.double Jacobian.double
    (by intros; rfl) (by intros; rfl) points scalars AdmittedG1.zero
  dsimp only [AdmittedG1.zero] at native
  let project : AdmittedG1 → curve.toAffine.Point := fun point => groupPoint point.point
  have defaults : project default = default := infinity_groupPoint
  have mathematical := nativeWindowed_map project defaults
    AdmittedG1.add (· + ·) AdmittedG1.double (fun point => point + point)
    (fun left right => add_groupPoint _ _ left.admitted right.admitted)
    (fun point => double_groupPoint _ point.admitted) points scalars AdmittedG1.zero
  rw [← native]
  change project (nativeWindowed points scalars AdmittedG1.zero AdmittedG1.add AdmittedG1.double) = _
  rw [mathematical]
  have zero : project AdmittedG1.zero = 0 := infinity_groupPoint
  rw [zero, native_group_sum]
  · simp only [Array.size_map, map_getBang project defaults]
    rfl
  · intro index bounded
    exact canonical index (by simpa using bounded)

theorem native_g1_raw_windowed_sum (points : Array Jacobian) (scalars : Array Nat)
    (admitted : ∀ point ∈ points, Admissible point)
    (canonical : ∀ index, index < points.size → scalars[index]! < LeanCrypto.Groth16.MSM.order) :
    groupPoint (nativeWindowed points scalars Jacobian.infinity Jacobian.add Jacobian.double) =
      ∑ index ∈ Finset.range points.size, scalars[index]! • groupPoint points[index]! := by
  let packed : Array AdmittedG1 := points.pmap (fun point proof => ⟨point, proof⟩) admitted
  have forgotten : packed.map AdmittedG1.point = points := by
    simp [packed, Array.map_pmap, Array.pmap_eq_map]
  have shape := congrArg Array.size forgotten
  simp only [Array.size_map] at shape
  have result := native_g1_windowed_sum packed scalars (by
    intro index bounded
    exact canonical index (by simpa only [shape] using bounded))
  rw [forgotten, shape] at result
  rw [result]
  apply Finset.sum_congr rfl
  intro index member
  have value := map_getBang AdmittedG1.point rfl packed index
  rw [forgotten] at value
  rw [value]

theorem native_g1_raw_windowed_admissible (points : Array Jacobian) (scalars : Array Nat)
    (admitted : ∀ point ∈ points, Admissible point) :
    Admissible (nativeWindowed points scalars Jacobian.infinity Jacobian.add Jacobian.double) := by
  let packed : Array AdmittedG1 := points.pmap (fun point proof => ⟨point, proof⟩) admitted
  have forgotten : packed.map AdmittedG1.point = points := by
    simp [packed, Array.map_pmap, Array.pmap_eq_map]
  have native := nativeWindowed_map AdmittedG1.point rfl
    AdmittedG1.add Jacobian.add AdmittedG1.double Jacobian.double
    (by intros; rfl) (by intros; rfl) packed scalars AdmittedG1.zero
  dsimp only [AdmittedG1.zero] at native
  rw [forgotten] at native
  rw [← native]
  exact (nativeWindowed packed scalars AdmittedG1.zero AdmittedG1.add AdmittedG1.double).admitted

end LeanCrypto.Proofs.WindowedMSM

#print axioms LeanCrypto.Proofs.WindowedMSM.native_g1_windowed_sum

#print axioms LeanCrypto.Proofs.WindowedMSM.native_g1_raw_windowed_sum

#print axioms LeanCrypto.Proofs.WindowedMSM.native_g1_raw_windowed_admissible
