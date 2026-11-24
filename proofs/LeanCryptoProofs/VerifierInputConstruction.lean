import LeanCryptoProofs.VerifierInputSource

noncomputable section
set_option autoImplicit false
namespace LeanCrypto.Proofs.NativeVerifier
open LeanCrypto.BN254.G1 LeanCrypto.Groth16.Verify
open BN254Group BN254Jacobian
local instance : Inhabited Affine := ⟨generator⟩

def inputContribution (key : VerifyingKey) (signals : Array Nat) (index : Nat) : curve.toAffine.Point :=
  signals[index]! • groupPoint (Jacobian.ofAffine key.ic[index + 1]!)

def publicInputMeaning (key : VerifyingKey) (signals : Array Nat) : curve.toAffine.Point :=
  groupPoint (Jacobian.ofAffine key.ic[0]!) +
    ((List.range' 0 signals.size).map (inputContribution key signals)).sum

theorem inputStep_construct (key : VerifyingKey) (signals : Array Nat)
    (counts : key.ic.size = signals.size + 1) (curves : key.ic.all (·.onCurve) = true)
    (canonical : signals.all (· < scalarPrime) = true)
    (index : Nat) (bounded : index < signals.size) (state : Jacobian) (admitted : Admissible state) :
    ∃ output, inputStep key signals state index = .ok output ∧ Admissible output ∧
      groupPoint output = groupPoint state + inputContribution key signals index := by
  have pointBound : index + 1 < key.ic.size := by omega
  have pointCurve : key.ic[index + 1]!.onCurve = true := by
    simpa only [getElem!_pos key.ic (index + 1) pointBound] using Array.all_eq_true.mp curves (index + 1) pointBound
  have pointAdmitted := ofAffine_admissible key.ic[index + 1]! pointCurve
  have scalarBound : signals[index]! < scalarPrime := by
    simpa only [getElem!_pos signals index bounded] using of_decide_eq_true (Array.all_eq_true.mp canonical index bounded)
  let output := state.add ((Jacobian.ofAffine key.ic[index + 1]!).scalarMul signals[index]!)
  refine ⟨output, ?_, add_preserves_curve_certified _ _ admitted (scalarMul_admissible _ _ pointAdmitted), ?_⟩
  · dsimp only [output]
    simp only [inputStep, getElem?_pos key.ic (index + 1) pointBound,
      getElem!_pos key.ic (index + 1) pointBound, pure, Except.pure]
  · rw [add_groupPoint _ _ admitted (scalarMul_admissible _ _ pointAdmitted),
      scalarMul_canonical_groupPoint _ _ pointAdmitted scalarBound]
    rfl

theorem inputFold_construct (key : VerifyingKey) (signals : Array Nat)
    (counts : key.ic.size = signals.size + 1) (curves : key.ic.all (·.onCurve) = true)
    (canonical : signals.all (· < scalarPrime) = true) :
    ∃ output, inputFold key signals key.ic[0]! = .ok output ∧ Admissible output ∧
      groupPoint output = publicInputMeaning key signals := by
  have loop (indices : List Nat) : ∀ state : Jacobian, Admissible state →
      (∀ index ∈ indices, index < signals.size) →
      ∃ output, indices.foldlM (inputStep key signals) state = .ok output ∧ Admissible output ∧
        groupPoint output = groupPoint state + (indices.map (inputContribution key signals)).sum := by
    induction indices with
    | nil => intro state admitted _; exact ⟨state, rfl, admitted, (add_zero _).symm⟩
    | cons index indices ih =>
      intro state admitted bounded
      obtain ⟨next, nextCall, nextAdmitted, nextMeaning⟩ := inputStep_construct key signals counts curves canonical
        index (bounded index (by simp)) state admitted
      obtain ⟨output, tailCall, outputAdmitted, outputMeaning⟩ := ih next nextAdmitted
        (fun j hj => bounded j (by simp [hj]))
      refine ⟨output, ?_, outputAdmitted, ?_⟩
      · simp only [List.foldlM_cons, nextCall, bind, Except.bind]
        exact tailCall
      · rw [outputMeaning, nextMeaning, List.map_cons, List.sum_cons, add_assoc]
  have firstBound : 0 < key.ic.size := by omega
  have firstCurve : key.ic[0]!.onCurve = true := by
    simpa only [getElem!_pos key.ic 0 firstBound] using Array.all_eq_true.mp curves 0 firstBound
  exact loop (List.range' 0 signals.size) (Jacobian.ofAffine key.ic[0]!) (ofAffine_admissible _ firstCurve)
    (fun index member => by obtain ⟨offset, bound, equal⟩ := List.mem_range'.mp member; omega)

theorem publicInputPoint_construct (key : VerifyingKey) (signals : Array Nat)
    (counts : key.ic.size = signals.size + 1) (limit : signals.size ≤ maxPublicSignals)
    (curves : key.ic.all (·.onCurve) = true) (canonical : signals.all (· < scalarPrime) = true)
    (finite : publicInputMeaning key signals ≠ 0) :
    ∃ (result : Affine) (onCurve : result.onCurve = true),
      publicInputPoint key signals = .ok result ∧ affinePoint result onCurve = publicInputMeaning key signals := by
  obtain ⟨output, constructed, admitted, meaning⟩ := inputFold_construct key signals counts curves canonical
  obtain ⟨affine, normalized, represented⟩ := toAffine_represents_groupPoint output admitted
  cases affine with
  | none => exact False.elim (finite (meaning.symm.trans represented))
  | some result =>
    obtain ⟨onCurve, resultMeaning⟩ := represented
    refine ⟨result, onCurve, ?_, resultMeaning.symm.trans meaning⟩
    have firstBound : 0 < key.ic.size := by omega
    unfold publicInputPoint
    rw [if_pos canonical]
    change nativeInputCandidate key signals = .ok result
    rw [input_candidate_source]
    have dimensionGuard : (key.ic.size != signals.size + 1 || decide (signals.size > maxPublicSignals)) = false := by
      simp [counts, Nat.not_lt.mpr limit]
    have curveGuard : (!(key.ic.all (·.onCurve))) = false := by rw [curves]; rfl
    simp only [dimensionGuard, curveGuard, Bool.false_eq_true, ↓reduceIte,
      getElem?_pos key.ic 0 firstBound, pure_bind]
    have origin : key.ic[0] = key.ic[0]! := (getElem!_pos key.ic 0 firstBound).symm
    rw [origin, constructed]
    simp only [bind, Except.bind]
    rw [normalized]
    rfl

end LeanCrypto.Proofs.NativeVerifier
#print axioms LeanCrypto.Proofs.NativeVerifier.inputStep_construct
#print axioms LeanCrypto.Proofs.NativeVerifier.inputFold_construct
#print axioms LeanCrypto.Proofs.NativeVerifier.publicInputPoint_construct
