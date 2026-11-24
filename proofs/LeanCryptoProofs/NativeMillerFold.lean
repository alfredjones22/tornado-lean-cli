import LeanCryptoProofs.NativeMillerStep
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing
open BN254G2Group BN254G2Jacobian

theorem millerFold_value (base : Affine) (baseCurve : base.onCurve = true)
    (subgroup : ((Jacobian.ofAffine base).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true)
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true) :
    ∃ (output : MProd Fp12 (Option Point)) (sum : Option Affine),
      millerFold (embedG2 base) (embedG1 evaluation) = .ok output ∧
      output.snd = sum.map embedG2 ∧
      Represents sum (LeanCrypto.BN254.G1.scalarPrime • affinePoint base baseCurve) ∧
      BN254Fp12.model output.fst ^ finalExponent = millerValue evaluation evaluationCurve
        LeanCrypto.BN254.G1.scalarPrime (embedTwistHom (affinePoint base baseCurve)) := by
  have loop (count : Nat) : ∀ (start : Nat) (state : MProd Fp12 (Option Point)) (sum : Option Affine),
      1 ≤ start → start + count = BN254MillerPrefixes.bits →
      state.snd = sum.map embedG2 →
      Represents sum (BN254MillerPrefixes.before start • affinePoint base baseCurve) →
      BN254Fp12.model state.fst ^ finalExponent = millerValue evaluation evaluationCurve
        (BN254MillerPrefixes.before start) (embedTwistHom (affinePoint base baseCurve)) →
      ∃ (output : MProd Fp12 (Option Point)) (last : Option Affine),
        (List.range' start count).foldlM
          (fun state step => millerStep (embedG2 base) (embedG1 evaluation) BN254MillerPrefixes.bits step state)
            state = .ok output ∧
        output.snd = last.map embedG2 ∧
        Represents last (LeanCrypto.BN254.G1.scalarPrime • affinePoint base baseCurve) ∧
        BN254Fp12.model output.fst ^ finalExponent = millerValue evaluation evaluationCurve
          LeanCrypto.BN254.G1.scalarPrime (embedTwistHom (affinePoint base baseCurve)) := by
    induction count with
    | zero =>
      intro start state sum positive finish shape represented value
      have atEnd : start = BN254MillerPrefixes.bits := by omega
      have final : BN254MillerPrefixes.before BN254MillerPrefixes.bits = LeanCrypto.BN254.G1.scalarPrime :=
        by decide +kernel
      rw [atEnd, final] at represented value
      exact ⟨state, sum, rfl, shape, represented, value⟩
    | succ count ih =>
      intro start state sum positive finish shape represented value
      have member : start ∈ BN254MillerPrefixes.steps := by
        apply List.mem_range'.mpr
        refine ⟨start - 1, ?_, ?_⟩ <;> omega
      have valid := BN254MillerPrefixes.valid_step start member
      have beforeNonzero := affine_prefix_nonzero base baseCurve subgroup
        (BN254MillerPrefixes.before start) valid.1 (by
          have bigger : BN254MillerPrefixes.before start ≤ 2 * BN254MillerPrefixes.before start := by omega
          exact bigger.trans_lt valid.2.1)
      obtain ⟨current, currentCurve, sumEq, currentMeaning⟩ :=
        represents_some_of_nonzero sum _ represented beforeNonzero
      have statePoint : state.snd = some (embedG2 current) := by rw [shape, sumEq]; rfl
      obtain ⟨next, nextSum, nextCall, nextShape, nextRep, nextValue⟩ :=
        millerStep_value base baseCurve subgroup evaluation evaluationCurve start member
          state current currentCurve statePoint currentMeaning.symm value
      rw [valid.2.2.2.2.2.1] at nextRep nextValue
      obtain ⟨output, last, tailCall, tailShape, tailRep, tailValue⟩ := ih (start + 1) next nextSum
        (by omega) (by omega) nextShape nextRep nextValue
      refine ⟨output, last, ?_, tailShape, tailRep, tailValue⟩
      simp only [List.range'_succ, List.foldlM_cons, nextCall, bind, Except.bind]
      exact tailCall
  refine loop (BN254MillerPrefixes.bits - 1) 1 ⟨Fp12.one, some (embedG2 base)⟩ (some base)
    (by decide) (by decide +kernel) rfl
    ⟨baseCurve, by rw [BN254MillerPrefixes.initial_prefix, one_nsmul]⟩ ?_
  change BN254Fp12.model Fp12.one ^ finalExponent = _
  rw [BN254Fp12.model_one, one_pow, BN254MillerPrefixes.initial_prefix, millerValue_one]

theorem miller_value (base : Affine) (baseCurve : base.onCurve = true)
    (subgroup : ((Jacobian.ofAffine base).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true)
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true) :
    ∃ result : Fp12, miller (embedG2 base) (embedG1 evaluation) = .ok result ∧
      BN254Fp12.model result ^ finalExponent = millerValue evaluation evaluationCurve
        LeanCrypto.BN254.G1.scalarPrime (embedTwistHom (affinePoint base baseCurve)) := by
  obtain ⟨output, sum, constructed, shape, represented, value⟩ :=
    millerFold_value base baseCurve subgroup evaluation evaluationCurve
  have annihilates : LeanCrypto.BN254.G1.scalarPrime • affinePoint base baseCurve = 0 := by
    rw [← ofAffine_groupPoint base baseCurve]
    exact (subgroup_check_iff _ (ofAffine_admissible base baseCurve)).1 subgroup
  rw [annihilates] at represented
  have noneEq := represents_zero_none sum represented
  rw [noneEq] at shape
  refine ⟨output.fst, ?_, value⟩
  rw [miller_source]
  simp only [embedG2_onCurve base baseCurve, embedG1_onCurve evaluation evaluationCurve,
    Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, constructed, bind, Except.bind]
  rw [shape]
  rfl

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.millerFold_value
#print axioms LeanCrypto.Proofs.BN254Tate.miller_value
