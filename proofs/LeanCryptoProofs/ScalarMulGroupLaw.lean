import LeanCryptoProofs.G1GroupLaw

/-! Actual native binary scalar multiplication and its established group
meaning. The source function reduces modulo q; no q-order theorem is assumed. -/
set_option autoImplicit false

namespace LeanCrypto.Proofs.BN254Group

open LeanCrypto.BN254.G1 LeanCrypto.Proofs.BN254Jacobian

theorem scalarMulLoop_admissible (factor accumulator : Jacobian) (scalar : Nat)
    (factorAdmitted : Admissible factor) (accumulatorAdmitted : Admissible accumulator) :
    Admissible (Jacobian.scalarMulLoop factor scalar accumulator) := by
  induction scalar using Nat.strong_induction_on generalizing factor accumulator with
  | h scalar ih =>
    rw [Jacobian.scalarMulLoop]
    split
    · exact accumulatorAdmitted
    · rename_i nonzero
      have nextFactor := double_preserves_curve_certified factor factorAdmitted
      have nextAccumulator : Admissible (if scalar % 2 = 1 then accumulator.add factor else accumulator) := by
        split
        · exact add_preserves_curve_certified accumulator factor accumulatorAdmitted factorAdmitted
        · exact accumulatorAdmitted
      exact ih (scalar / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero nonzero) (by decide))
        _ _ nextFactor nextAccumulator

/-- Universal invariant of the actual total binary backend. -/
theorem scalarMulLoop_groupPoint (factor accumulator : Jacobian) (scalar : Nat)
    (factorAdmitted : Admissible factor) (accumulatorAdmitted : Admissible accumulator) :
    groupPoint (Jacobian.scalarMulLoop factor scalar accumulator) =
      groupPoint accumulator + scalar • groupPoint factor := by
  induction scalar using Nat.strong_induction_on generalizing factor accumulator with
  | h scalar ih =>
    rw [Jacobian.scalarMulLoop]
    split
    · rename_i zero
      simp [zero]
    · rename_i nonzero
      have smaller : scalar / 2 < scalar := Nat.div_lt_self (Nat.pos_of_ne_zero nonzero) (by decide)
      have nextFactor := double_preserves_curve_certified factor factorAdmitted
      by_cases odd : scalar % 2 = 1
      · simp only [odd, ↓reduceIte]
        rw [ih (scalar / 2) smaller _ _ nextFactor
          (add_preserves_curve_certified accumulator factor accumulatorAdmitted factorAdmitted),
          add_groupPoint accumulator factor accumulatorAdmitted factorAdmitted,
          double_groupPoint factor factorAdmitted]
        have exponent : scalar / 2 + scalar / 2 + 1 = scalar := by
          have divide := Nat.mod_add_div scalar 2
          omega
        calc
          groupPoint accumulator + groupPoint factor +
              (scalar / 2) • (groupPoint factor + groupPoint factor) =
              groupPoint accumulator + (scalar / 2 + scalar / 2 + 1) • groupPoint factor := by
            simp only [nsmul_add, add_nsmul, one_nsmul]
            ac_rfl
          _ = _ := by rw [exponent]
      · simp only [odd, ↓reduceIte]
        rw [ih (scalar / 2) smaller _ _ nextFactor accumulatorAdmitted,
          double_groupPoint factor factorAdmitted, nsmul_add, ← add_nsmul]
        have exponent : scalar / 2 + scalar / 2 = scalar := by
          have bound := Nat.mod_lt scalar (by decide : 0 < 2)
          have divide := Nat.mod_add_div scalar 2
          omega
        rw [exponent]

theorem scalarMul_admissible (point : Jacobian) (scalar : Nat) (admitted : Admissible point) :
    Admissible (point.scalarMul scalar) :=
  scalarMulLoop_admissible point Jacobian.infinity (scalar % scalarPrime) admitted infinity_admissible

/-- Exact semantics of the public native function, including its existing
modulo-q input reduction. This does not assert that q annihilates the group. -/
theorem scalarMul_groupPoint (point : Jacobian) (scalar : Nat) (admitted : Admissible point) :
    groupPoint (point.scalarMul scalar) = (scalar % scalarPrime) • groupPoint point := by
  rw [Jacobian.scalarMul,
    scalarMulLoop_groupPoint point Jacobian.infinity (scalar % scalarPrime) admitted infinity_admissible,
    infinity_groupPoint, zero_add]

theorem scalarMul_canonical_groupPoint (point : Jacobian) (scalar : Nat)
    (admitted : Admissible point) (canonical : scalar < scalarPrime) :
    groupPoint (point.scalarMul scalar) = scalar • groupPoint point := by
  rw [scalarMul_groupPoint point scalar admitted, Nat.mod_eq_of_lt canonical]

theorem scalarMul_zero (point : Jacobian) : point.scalarMul 0 = Jacobian.infinity := by
  simp [Jacobian.scalarMul, Jacobian.scalarMulLoop]

theorem scalarMul_one (point : Jacobian) : point.scalarMul 1 = point := by
  have reduced : 1 % scalarPrime = 1 := Nat.mod_eq_of_lt (by decide)
  simp [Jacobian.scalarMul, reduced, Jacobian.scalarMulLoop, add_left_infinity]

end LeanCrypto.Proofs.BN254Group

#print axioms LeanCrypto.Proofs.BN254Group.scalarMulLoop_admissible
#print axioms LeanCrypto.Proofs.BN254Group.scalarMulLoop_groupPoint
#print axioms LeanCrypto.Proofs.BN254Group.scalarMul_admissible
#print axioms LeanCrypto.Proofs.BN254Group.scalarMul_groupPoint
#print axioms LeanCrypto.Proofs.BN254Group.scalarMul_canonical_groupPoint
#print axioms LeanCrypto.Proofs.BN254Group.scalarMul_zero
#print axioms LeanCrypto.Proofs.BN254Group.scalarMul_one
