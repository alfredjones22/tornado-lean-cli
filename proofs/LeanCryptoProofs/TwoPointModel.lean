import LeanCryptoProofs.ButterflyModel

namespace LeanCrypto.Proofs.BN254Fr

open LeanCrypto.Groth16

/-- The exact native normalization factor constructs a multiplicative half. -/
theorem two_point_half : (2 : ZMod Q) * model ((Q + 1) / 2) = 1 := by
  have native : FFT.mul 2 ((Q + 1) / 2) = 1 := by decide +kernel
  have represented := congrArg model native
  simpa only [model_mul, model, Nat.cast_ofNat, Nat.cast_one] using represented

theorem two_point_half_inverse [Fact Q.Prime] :
    model ((Q + 1) / 2) = (2 : ZMod Q)⁻¹ := by
  have nonzero : (2 : ZMod Q) ≠ 0 := by
    change model 2 ≠ 0
    intro equal
    exact (by decide : (2 : Nat) % Q ≠ 0) ((model_zero_iff 2).1 equal)
  apply mul_left_cancel₀ nonzero
  rw [two_point_half, mul_inv_cancel₀ nonzero]

/-- The actual native forward transform constructs the size-two DFT. -/
theorem fft_two_point_field (a b : Nat) (aBound : a < Q) (bBound : b < Q) :
    (FFT.fft #[a, b]).map (fun values => values.map model) =
      .ok #[model a + model b, model a - model b] := by
  rw [FFT.fft_two_point a b aBound bBound]
  simp [Except.map]

/-- The actual native inverse constructs the normalized size-two inverse DFT. -/
theorem ifft_two_point_field [Fact Q.Prime] (a b : Nat) (aBound : a < Q) (bBound : b < Q) :
    (FFT.ifft #[a, b]).map (fun values => values.map model) =
      .ok #[(model a + model b) / 2, (model a - model b) / 2] := by
  rw [FFT.ifft_two_point a b aBound bBound]
  simp [Except.map, two_point_half_inverse, div_eq_mul_inv]

end LeanCrypto.Proofs.BN254Fr

#print axioms LeanCrypto.Proofs.BN254Fr.two_point_half
#print axioms LeanCrypto.Proofs.BN254Fr.two_point_half_inverse
#print axioms LeanCrypto.Proofs.BN254Fr.fft_two_point_field
#print axioms LeanCrypto.Proofs.BN254Fr.ifft_two_point_field
