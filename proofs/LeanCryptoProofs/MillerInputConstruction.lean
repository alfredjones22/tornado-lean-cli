import LeanCryptoProofs.TateLineGroup
import LeanCryptoProofs.MillerPrefixes
import LeanCryptoProofs.G2ScalarSubgroup
noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.BN254Tate
open LeanCrypto.BN254.G2 LeanCrypto.BN254.PairingField LeanCrypto.BN254.TatePairing
open BN254G2Group BN254G2Jacobian

theorem ofAffine_groupPoint (point : Affine) (onCurve : point.onCurve = true) :
    groupPoint (Jacobian.ofAffine point) = affinePoint point onCurve := by
  have finite : BN254Fp2.model (Jacobian.ofAffine point).z ≠ 0 := by simp [Jacobian.ofAffine]
  have equation : ProjectiveEquation (Jacobian.ofAffine point) := by
    simpa [ProjectiveEquation, Jacobian.ofAffine] using (BN254Fp2.affine_onCurve_iff point).1 onCurve
  simpa only [BN254G2Jacobian.normalized_ofAffine] using
    normalized_groupPoint (Jacobian.ofAffine point) finite equation

theorem represents_some_of_nonzero (result : Option Affine) (meaning : curve.toAffine.Point)
    (represented : Represents result meaning) (nonzero : meaning ≠ 0) :
    ∃ (point : Affine) (onCurve : point.onCurve = true),
      result = some point ∧ meaning = affinePoint point onCurve := by
  cases result with
  | none => exact False.elim (nonzero represented)
  | some point =>
    obtain ⟨onCurve, equal⟩ := represented
    exact ⟨point, onCurve, rfl, equal⟩

theorem represents_zero_none (result : Option Affine) (represented : Represents result 0) :
    result = none := by
  cases result with
  | none => rfl
  | some point =>
    obtain ⟨onCurve, impossible⟩ := represented
    unfold affinePoint at impossible
    cases impossible

theorem affine_prefix_nonzero (base : Affine) (onCurve : base.onCurve = true)
    (subgroup : ((Jacobian.ofAffine base).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true)
    (index : Nat) (positive : 0 < index) (proper : index < LeanCrypto.BN254.G1.scalarPrime) :
    index • affinePoint base onCurve ≠ 0 := by
  rw [← ofAffine_groupPoint base onCurve]
  exact affine_checked_prefix_nonzero base onCurve subgroup index positive proper

theorem millerStep_construct (base : Affine) (baseCurve : base.onCurve = true)
    (subgroup : ((Jacobian.ofAffine base).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true)
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true)
    (step : Nat) (member : step ∈ BN254MillerPrefixes.steps)
    (state : MProd Fp12 (Option Point)) (current : Affine) (currentCurve : current.onCurve = true)
    (statePoint : state.snd = some (embedG2 current))
    (currentMeaning : affinePoint current currentCurve =
      BN254MillerPrefixes.before step • affinePoint base baseCurve) :
    ∃ (output : MProd Fp12 (Option Point)) (sum : Option Affine),
      millerStep (embedG2 base) (embedG1 evaluation) BN254MillerPrefixes.bits step state = .ok output ∧
      output.snd = sum.map embedG2 ∧
      Represents sum (BN254MillerPrefixes.after step • affinePoint base baseCurve) := by
  obtain ⟨positive, properDouble, prefixEq, _, _, _, _⟩ := BN254MillerPrefixes.valid_step step member
  obtain ⟨doubledFactor, doubledSum, doubledCall, doubledRep⟩ :=
    twist_line_construct current current currentCurve currentCurve evaluation evaluationCurve
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
  by_cases odd : BN254MillerPrefixes.digit step = 1
  · obtain ⟨addedFactor, addedSum, addedCall, addedRep⟩ :=
      twist_line_construct doubled base doubledCurve baseCurve evaluation evaluationCurve
    have afterEq : BN254MillerPrefixes.after step = 2 * BN254MillerPrefixes.before step + 1 := by
      rw [prefixEq, odd]
    have addedMeaning : affinePoint doubled doubledCurve + affinePoint base baseCurve =
        BN254MillerPrefixes.after step • affinePoint base baseCurve := by
      rw [afterEq, add_nsmul, one_nsmul, doubledMeaning]
    rw [addedMeaning] at addedRep
    refine ⟨⟨(state.fst.square.mul doubledFactor).mul addedFactor, addedSum.map embedG2⟩,
      addedSum, ?_, rfl, addedRep⟩
    simp [millerStep, statePoint, doubledCall, bit, odd, addedCall, bind, Except.bind]
    rfl
  · have digitBound : BN254MillerPrefixes.digit step < 2 := Nat.mod_lt _ (by decide)
    have even : BN254MillerPrefixes.digit step = 0 := by omega
    have afterEq : BN254MillerPrefixes.after step = 2 * BN254MillerPrefixes.before step := by
      rw [prefixEq, even, Nat.add_zero]
    refine ⟨⟨state.fst.square.mul doubledFactor, some (embedG2 doubled)⟩,
      some doubled, ?_, rfl, doubledCurve, ?_⟩
    · simp [millerStep, statePoint, doubledCall, bit, even, bind, Except.bind]
      rfl
    · rw [afterEq]
      exact doubledMeaning

theorem millerFold_construct (base : Affine) (baseCurve : base.onCurve = true)
    (subgroup : ((Jacobian.ofAffine base).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true)
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true) :
    ∃ (output : MProd Fp12 (Option Point)) (sum : Option Affine),
      millerFold (embedG2 base) (embedG1 evaluation) = .ok output ∧
      output.snd = sum.map embedG2 ∧
      Represents sum (LeanCrypto.BN254.G1.scalarPrime • affinePoint base baseCurve) := by
  have loop (count : Nat) : ∀ (start : Nat) (state : MProd Fp12 (Option Point)) (sum : Option Affine),
      1 ≤ start → start + count = BN254MillerPrefixes.bits →
      state.snd = sum.map embedG2 →
      Represents sum (BN254MillerPrefixes.before start • affinePoint base baseCurve) →
      ∃ (output : MProd Fp12 (Option Point)) (last : Option Affine),
        (List.range' start count).foldlM
          (fun state step => millerStep (embedG2 base) (embedG1 evaluation) BN254MillerPrefixes.bits step state)
            state = .ok output ∧
        output.snd = last.map embedG2 ∧
        Represents last (LeanCrypto.BN254.G1.scalarPrime • affinePoint base baseCurve) := by
    induction count with
    | zero =>
      intro start state sum positive finish shape represented
      have atEnd : start = BN254MillerPrefixes.bits := by omega
      have final : BN254MillerPrefixes.before BN254MillerPrefixes.bits = LeanCrypto.BN254.G1.scalarPrime :=
        by decide +kernel
      rw [atEnd, final] at represented
      exact ⟨state, sum, rfl, shape, represented⟩
    | succ count ih =>
      intro start state sum positive finish shape represented
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
      obtain ⟨next, nextSum, nextCall, nextShape, nextRep⟩ :=
        millerStep_construct base baseCurve subgroup evaluation evaluationCurve start member
          state current currentCurve statePoint currentMeaning.symm
      rw [valid.2.2.2.2.2.1] at nextRep
      obtain ⟨output, last, tailCall, tailShape, tailRep⟩ := ih (start + 1) next nextSum
        (by omega) (by omega) nextShape nextRep
      refine ⟨output, last, ?_, tailShape, tailRep⟩
      simp only [List.range'_succ, List.foldlM_cons, nextCall, bind, Except.bind]
      exact tailCall
  exact loop (BN254MillerPrefixes.bits - 1) 1 ⟨Fp12.one, some (embedG2 base)⟩ (some base)
    (by decide) (by decide +kernel) rfl ⟨baseCurve, by rw [BN254MillerPrefixes.initial_prefix, one_nsmul]⟩

/-- Every independently on-curve finite G1 input and on-twist q-torsion G2
input constructs a successful result of the actual original Miller program.
No successful arithmetic, step, fold, or final-check call is assumed. -/
theorem miller_construct (base : Affine) (baseCurve : base.onCurve = true)
    (subgroup : ((Jacobian.ofAffine base).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity = true)
    (evaluation : LeanCrypto.BN254.G1.Affine) (evaluationCurve : evaluation.onCurve = true) :
    ∃ result : Fp12, miller (embedG2 base) (embedG1 evaluation) = .ok result := by
  obtain ⟨output, sum, constructed, shape, represented⟩ :=
    millerFold_construct base baseCurve subgroup evaluation evaluationCurve
  have annihilates : LeanCrypto.BN254.G1.scalarPrime • affinePoint base baseCurve = 0 := by
    rw [← ofAffine_groupPoint base baseCurve]
    exact (subgroup_check_iff _ (ofAffine_admissible base baseCurve)).1 subgroup
  rw [annihilates] at represented
  have noneEq := represents_zero_none sum represented
  rw [noneEq] at shape
  refine ⟨output.fst, ?_⟩
  rw [miller_source]
  simp only [embedG2_onCurve base baseCurve, embedG1_onCurve evaluation evaluationCurve,
    Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte, constructed, bind, Except.bind]
  rw [shape]
  rfl

end LeanCrypto.Proofs.BN254Tate
#print axioms LeanCrypto.Proofs.BN254Tate.ofAffine_groupPoint
#print axioms LeanCrypto.Proofs.BN254Tate.represents_some_of_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.represents_zero_none
#print axioms LeanCrypto.Proofs.BN254Tate.affine_prefix_nonzero
#print axioms LeanCrypto.Proofs.BN254Tate.millerStep_construct
#print axioms LeanCrypto.Proofs.BN254Tate.millerFold_construct
#print axioms LeanCrypto.Proofs.BN254Tate.miller_construct
