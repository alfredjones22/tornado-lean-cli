import LeanCryptoProofs.NativeMillerValue
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing
open BN254G2Group BN254G2Jacobian

theorem square_final_power (value : BN254Fp12.Field) :
    (value ^ 2) ^ finalExponent = (value ^ finalExponent) ^ 2 := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 finalExponent]

theorem millerStep_value (base : Affine) (baseCurve : base.onCurve = true)
    (subgroup : ((Jacobian.ofAffine base).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true)
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true)
    (step : Nat) (member : step ∈ BN254MillerPrefixes.steps)
    (state : MProd Fp12 (Option Point)) (current : Affine) (currentCurve : current.onCurve = true)
    (statePoint : state.snd = some (embedG2 current))
    (currentMeaning : affinePoint current currentCurve =
      BN254MillerPrefixes.before step • affinePoint base baseCurve)
    (stateValue : BN254Fp12.model state.fst ^ finalExponent = millerValue evaluation evaluationCurve
      (BN254MillerPrefixes.before step) (embedTwistHom (affinePoint base baseCurve))) :
    ∃ (output : MProd Fp12 (Option Point)) (sum : Option Affine),
      millerStep (embedG2 base) (embedG1 evaluation) BN254MillerPrefixes.bits step state = .ok output ∧
      output.snd = sum.map embedG2 ∧
      Represents sum (BN254MillerPrefixes.after step • affinePoint base baseCurve) ∧
      BN254Fp12.model output.fst ^ finalExponent = millerValue evaluation evaluationCurve
        (BN254MillerPrefixes.after step) (embedTwistHom (affinePoint base baseCurve)) := by
  obtain ⟨positive, properDouble, prefixEq, _, _, _, _⟩ := BN254MillerPrefixes.valid_step step member
  obtain ⟨doubledFactor, doubledSum, doubledCall, doubledRep⟩ :=
    twist_line_construct current current currentCurve currentCurve evaluation evaluationCurve
  have doubleValue := native_line_reduced current current currentCurve currentCurve
    evaluation evaluationCurve doubledFactor (doubledSum.map embedG2) doubledCall
  have currentTwist : embedTwistHom (affinePoint current currentCurve) =
      BN254MillerPrefixes.before step • embedTwistHom (affinePoint base baseCurve) := by
    rw [currentMeaning, map_nsmul]
  rw [currentTwist] at doubleValue
  have doubleMeaning : affinePoint current currentCurve + affinePoint current currentCurve =
      (2 * BN254MillerPrefixes.before step) • affinePoint base baseCurve := by
    rw [currentMeaning, two_mul, add_nsmul]
  rw [doubleMeaning] at doubledRep
  have doubledNonzero := affine_prefix_nonzero base baseCurve subgroup
    (2 * BN254MillerPrefixes.before step) (by omega) properDouble
  obtain ⟨doubled, doubledCurve, sumEq, doubledMeaning⟩ :=
    represents_some_of_nonzero doubledSum _ doubledRep doubledNonzero
  rw [sumEq] at doubledCall
  have bit : LeanCrypto.BN254.G1.scalarPrime / 2 ^ (BN254MillerPrefixes.bits - step - 1) % 2 =
      BN254MillerPrefixes.digit step := rfl
  have doubleAccumulator : BN254Fp12.model (state.fst.square.mul doubledFactor) ^ finalExponent =
      millerValue evaluation evaluationCurve (2 * BN254MillerPrefixes.before step)
        (embedTwistHom (affinePoint base baseCurve)) := by
    rw [BN254Fp12.model_mul, BN254Fp12.model_square, mul_pow, square_final_power,
      stateValue, doubleValue, millerValue_double]
  by_cases odd : BN254MillerPrefixes.digit step = 1
  · obtain ⟨addedFactor, addedSum, addedCall, addedRep⟩ :=
      twist_line_construct doubled base doubledCurve baseCurve evaluation evaluationCurve
    have addedValue := native_line_reduced doubled base doubledCurve baseCurve
      evaluation evaluationCurve addedFactor (addedSum.map embedG2) addedCall
    have doubledTwist : embedTwistHom (affinePoint doubled doubledCurve) =
        (2 * BN254MillerPrefixes.before step) • embedTwistHom (affinePoint base baseCurve) := by
      rw [← doubledMeaning, map_nsmul]
    rw [doubledTwist] at addedValue
    have afterEq : BN254MillerPrefixes.after step = 2 * BN254MillerPrefixes.before step + 1 := by
      rw [prefixEq, odd]
    have addedMeaning : affinePoint doubled doubledCurve + affinePoint base baseCurve =
        BN254MillerPrefixes.after step • affinePoint base baseCurve := by
      rw [afterEq, add_nsmul, one_nsmul, ← doubledMeaning]
    rw [addedMeaning] at addedRep
    refine ⟨⟨(state.fst.square.mul doubledFactor).mul addedFactor, addedSum.map embedG2⟩,
      addedSum, ?_, rfl, addedRep, ?_⟩
    · simp [millerStep, statePoint, doubledCall, bit, odd, addedCall, bind, Except.bind]
      rfl
    · change BN254Fp12.model ((state.fst.square.mul doubledFactor).mul addedFactor) ^ finalExponent = _
      rw [BN254Fp12.model_mul, mul_pow, doubleAccumulator, addedValue, afterEq, millerValue_succ]
  · have digitBound : BN254MillerPrefixes.digit step < 2 := Nat.mod_lt _ (by decide)
    have even : BN254MillerPrefixes.digit step = 0 := by omega
    have afterEq : BN254MillerPrefixes.after step = 2 * BN254MillerPrefixes.before step := by
      rw [prefixEq, even, Nat.add_zero]
    refine ⟨⟨state.fst.square.mul doubledFactor, some (embedG2 doubled)⟩,
      some doubled, ?_, rfl, ⟨doubledCurve, ?_⟩, ?_⟩
    · simp [millerStep, statePoint, doubledCall, bit, even, bind, Except.bind]
      rfl
    · rw [afterEq]
      exact doubledMeaning
    · rw [afterEq]
      exact doubleAccumulator

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.square_final_power
#print axioms LeanCrypto.Proofs.BN254Tate.millerStep_value
