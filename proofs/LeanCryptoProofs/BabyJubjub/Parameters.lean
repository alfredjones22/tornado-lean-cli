import LeanCryptoProofs.BabyJubjub.EdwardsComplete

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace LeanCrypto.Proofs.BabyJubjubComplete
open LeanCrypto.Proofs.BN254Fr

/-- The actual BabyJubJub Edwards coefficient has this kernel-checked square root. -/
theorem edwards_a_square : IsSquare (168700 : ZMod Q) := by
  refine ⟨7214280148105020021932206872019688659210616427216992810330019057549499971851, ?_⟩
  decide +kernel

theorem edwards_d_legendre : (168696 : ZMod Q) ^ ((Q - 1) / 2) = -1 := by
  have computed : LeanCrypto.Groth16.FFT.powMod 168696 ((Q - 1) / 2) = Q - 1 := by decide +kernel
  have represented := model_powMod 168696 ((Q - 1) / 2)
  rw [computed] at represented
  calc
    _ = model (Q - 1) := represented.symm
    _ = -1 := by decide +kernel

theorem edwards_d_nonsquare : ¬ IsSquare (168696 : ZMod Q) := by
  rintro ⟨root, equal⟩
  have nonzero : root ≠ 0 := by
    intro zero
    rw [zero, mul_zero] at equal
    exact (by decide +kernel : (168696 : ZMod Q) ≠ 0) equal
  have fermat := model_fermat root nonzero
  have exponent : 2 * ((Q - 1) / 2) = Q - 1 := by decide +kernel
  have squarePow : (168696 : ZMod Q) ^ ((Q - 1) / 2) = 1 := by
    rw [equal, ← pow_two, ← pow_mul, exponent]
    exact fermat
  have opposite := edwards_d_legendre
  rw [squarePow] at opposite
  exact (by decide +kernel : (1 : ZMod Q) ≠ -1) opposite

theorem babyjub_complete_denominators (x1 y1 x2 y2 : ZMod Q)
    (first : Edwards 168700 168696 x1 y1) (second : Edwards 168700 168696 x2 y2) :
    1 + 168696*x1*x2*y1*y2 ≠ 0 ∧ 1 - 168696*x1*x2*y1*y2 ≠ 0 :=
  complete_denominators 168700 168696 x1 y1 x2 y2 first second edwards_a_square edwards_d_nonsquare

end LeanCrypto.Proofs.BabyJubjubComplete
#print axioms LeanCrypto.Proofs.BabyJubjubComplete.edwards_a_square
#print axioms LeanCrypto.Proofs.BabyJubjubComplete.edwards_d_legendre
#print axioms LeanCrypto.Proofs.BabyJubjubComplete.edwards_d_nonsquare
#print axioms LeanCrypto.Proofs.BabyJubjubComplete.babyjub_complete_denominators
