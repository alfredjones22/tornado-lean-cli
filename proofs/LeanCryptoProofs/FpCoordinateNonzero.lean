import LeanCryptoProofs.CertifiedFields

set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254G1Coordinates
open LeanCrypto.BN254.G1 BN254Fp

set_option maxRecDepth 8192
set_option maxHeartbeats 0 in
theorem three_nonsquare_certificate :
    (Fp.ofNat 3).pow ((P - 1) / 2) != Fp.one := by decide +kernel

set_option maxRecDepth 8192
set_option maxHeartbeats 0 in
theorem negative_three_noncube_certificate :
    (Fp.ofNat (P - 3)).pow ((P - 1) / 3) != Fp.one := by decide +kernel

theorem native_power_certificate (value : Fp) (exponent : Nat)
    (certificate : value.pow exponent != Fp.one) : model value ^ exponent ≠ 1 := by
  intro equal
  rw [← model_pow] at equal
  have nativeEqual : value.pow exponent = Fp.one := model_injective (equal.trans model_one.symm)
  rw [nativeEqual] at certificate
  change false = true at certificate
  cases certificate

theorem no_square_three (value : ZMod P) : value ^ 2 ≠ 3 := by
  intro square
  have nonzero : value ≠ 0 := by
    intro zero
    rw [zero, zero_pow (by decide)] at square
    exact (by decide +kernel : (0 : ZMod P) ≠ 3) square
  have cannot : (3 : ZMod P) ^ ((P - 1) / 2) ≠ 1 := by
    simpa only [model_ofNat, Nat.cast_ofNat] using
      native_power_certificate (Fp.ofNat 3) _ three_nonsquare_certificate
  apply cannot
  rw [← square, ← pow_mul, show 2 * ((P - 1) / 2) = P - 1 by decide +kernel]
  exact model_fermat value nonzero

theorem no_cube_negative_three (value : ZMod P) : value ^ 3 ≠ -3 := by
  intro cube
  have nonzero : value ≠ 0 := by
    intro zero
    rw [zero, zero_pow (by decide)] at cube
    exact (by decide +kernel : (0 : ZMod P) ≠ -3) cube
  have negativeThree : model (Fp.ofNat (P - 3)) = -3 := by decide +kernel
  have cannot : (-3 : ZMod P) ^ ((P - 1) / 3) ≠ 1 := by
    rw [← negativeThree]
    exact native_power_certificate (Fp.ofNat (P - 3)) _ negative_three_noncube_certificate
  apply cannot
  rw [← cube, ← pow_mul, show 3 * ((P - 1) / 3) = P - 1 by decide +kernel]
  exact model_fermat value nonzero

theorem affine_x_nonzero (point : Affine) (onCurve : point.onCurve = true) : model point.x ≠ 0 := by
  intro zero
  have equation := (affine_onCurve_iff point).1 onCurve
  rw [zero, zero_pow (by decide), zero_add] at equation
  exact no_square_three _ equation

theorem affine_y_nonzero (point : Affine) (onCurve : point.onCurve = true) : model point.y ≠ 0 := by
  intro zero
  have equation := (affine_onCurve_iff point).1 onCurve
  rw [zero, zero_pow (by decide)] at equation
  apply no_cube_negative_three (model point.x)
  exact eq_neg_of_add_eq_zero_left equation.symm

end LeanCrypto.Proofs.BN254G1Coordinates
#print axioms LeanCrypto.Proofs.BN254G1Coordinates.three_nonsquare_certificate
#print axioms LeanCrypto.Proofs.BN254G1Coordinates.negative_three_noncube_certificate
#print axioms LeanCrypto.Proofs.BN254G1Coordinates.native_power_certificate
#print axioms LeanCrypto.Proofs.BN254G1Coordinates.no_square_three
#print axioms LeanCrypto.Proofs.BN254G1Coordinates.no_cube_negative_three
#print axioms LeanCrypto.Proofs.BN254G1Coordinates.affine_x_nonzero
#print axioms LeanCrypto.Proofs.BN254G1Coordinates.affine_y_nonzero
