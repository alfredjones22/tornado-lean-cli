import LeanCrypto.Groth16.R1CS
import LeanCryptoProofs.CertifiedFields
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

namespace LeanCrypto.Proofs.R1CSModel

open LeanCrypto.Groth16.R1CS
open LeanCrypto.Proofs.BN254Fr

def RowAdmitted (witness : Array Nat) (row : LinearCombination) : Prop :=
  ∀ term ∈ row.terms, term.1 < witness.size ∧ term.2 < Q

def linearValue (witness : Array Nat) (row : LinearCombination) : ZMod Q :=
  ((row.terms.toList.map fun term => model term.2 * model witness[term.1]!).sum)

def ConstraintSatisfied (witness : Array Nat) (row : Constraint) : Prop :=
  linearValue witness row.a * linearValue witness row.b = linearValue witness row.c

theorem row_admitted_iff (witness : Array Nat) (row : LinearCombination) :
    RowAdmitted witness row ↔ rowIndicesValid witness row = true := by
  simp only [RowAdmitted, rowIndicesValid, Array.all_eq_true]
  constructor
  · intro admitted index bounded
    have member : row.terms[index] ∈ row.terms := Array.getElem_mem bounded
    have result := admitted _ member
    simpa [Bool.and_eq_true, Q, LeanCrypto.Groth16.FFT.modulus, scalarPrime] using result
  · intro checked term member
    obtain ⟨index, bounded, equal⟩ := Array.mem_iff_getElem.mp member
    have result := checked index bounded
    simpa [← equal, Bool.and_eq_true, Q, LeanCrypto.Groth16.FFT.modulus, scalarPrime] using result

theorem fold_value (terms : List (Nat × Nat)) (witness : Array Nat) (accumulator : Nat) :
    model (terms.foldl (fun acc term => acc + term.2 * witness[term.1]!) accumulator) =
      model accumulator + (terms.map fun term => model term.2 * model witness[term.1]!).sum := by
  induction terms generalizing accumulator with
  | nil => simp
  | cons term rest ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    simp only [model, Nat.cast_add, Nat.cast_mul]
    ring

def rowValue (witness : Array Nat) (row : LinearCombination) : Nat :=
  (row.terms.foldl (fun acc term => acc + term.2 * witness[term.1]!) 0) % scalarPrime

theorem rowValue_bounded (witness : Array Nat) (row : LinearCombination) :
    rowValue witness row < Q := Nat.mod_lt _ (by decide)

theorem rowValue_model (witness : Array Nat) (row : LinearCombination) :
    model (rowValue witness row) = linearValue witness row := by
  unfold rowValue linearValue
  change model ((row.terms.foldl (fun acc term => acc + term.2 * witness[term.1]!) 0) % Q) = _
  rw [model_mod, ← Array.foldl_toList, fold_value]
  simp [model]

/-- Actual sparse-row evaluation is constructed from independent index and
coefficient conditions and has the mathematical linear-combination value. -/
theorem evaluateRow_construct (witness : Array Nat) (row : LinearCombination)
    (admitted : RowAdmitted witness row) :
    evaluateRow witness row = .ok (rowValue witness row) ∧
      model (rowValue witness row) = linearValue witness row ∧ rowValue witness row < Q := by
  exact ⟨by simp [evaluateRow, (row_admitted_iff witness row).mp admitted, rowValue],
    rowValue_model witness row, rowValue_bounded witness row⟩

theorem checkConstraint_construct (witness : Array Nat) (row : Constraint)
    (a : RowAdmitted witness row.a) (b : RowAdmitted witness row.b)
    (c : RowAdmitted witness row.c) (equation : ConstraintSatisfied witness row) :
    checkConstraint witness row = .ok true := by
  have ea := evaluateRow_construct witness row.a a
  have eb := evaluateRow_construct witness row.b b
  have ec := evaluateRow_construct witness row.c c
  have equality : (rowValue witness row.a * rowValue witness row.b) % scalarPrime = rowValue witness row.c := by
    apply canonical_injective (Nat.mod_lt _ (by decide)) ec.2.2
    change model ((rowValue witness row.a * rowValue witness row.b) % Q) = _
    rw [model_mod]
    simp only [model, Nat.cast_mul]
    change model (rowValue witness row.a) * model (rowValue witness row.b) = model (rowValue witness row.c)
    rw [ea.2.1, eb.2.1, ec.2.1]
    exact equation
  simp [checkConstraint, ea.1, eb.1, ec.1, equality]

theorem checked_list_loop (indices : List Nat) (check : Nat → Except String Bool)
    (error : Nat → String) (accepted : ∀ index ∈ indices, check index = .ok true) :
    (ForIn.forIn indices () (fun index _ => do
      if !(← check index) then throw (error index)
      pure (ForInStep.yield ())) : Except String Unit) = .ok () := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    have first := accepted index (by simp)
    have tail := ih (fun value member => accepted value (by simp [member]))
    simpa only [List.forIn_cons, first, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Except.pure, Except.bind] using tail

/-- The complete actual checker constructs success from mathematical row
equations, canonical data and shape, without assuming any checker accepted. -/
theorem checkCircuit_construct (circuit : Circuit) (witness : Array Nat)
    (shape : witness.size = circuit.nVars) (constant : witness[0]? = some 1)
    (canonical : ∀ value ∈ witness, value < Q)
    (rowsAdmitted : ∀ row ∈ circuit.constraints,
      RowAdmitted witness row.a ∧ RowAdmitted witness row.b ∧ RowAdmitted witness row.c)
    (equations : ∀ row ∈ circuit.constraints, ConstraintSatisfied witness row) :
    checkCircuit circuit witness = .ok circuit.constraints.size := by
  have fields : witness.any (fun value => value >= scalarPrime) = false := by
    apply Array.any_eq_false.mpr
    intro index bounded forbidden
    have value := canonical witness[index] (Array.getElem_mem bounded)
    exact (Nat.not_le_of_lt value) (of_decide_eq_true forbidden)
  have checked : ∀ index ∈ List.range' 0 circuit.constraints.size,
      checkConstraint witness circuit.constraints[index]! = .ok true := by
    intro index member
    have bounded : index < circuit.constraints.size := by
      have := List.mem_range'.mp member
      omega
    have present : circuit.constraints[index]! ∈ circuit.constraints := by
      simpa only [getElem!_pos circuit.constraints index bounded] using Array.getElem_mem bounded
    obtain ⟨a, b, c⟩ := rowsAdmitted _ present
    exact checkConstraint_construct witness _ a b c (equations _ present)
  have completed := checked_list_loop (List.range' 0 circuit.constraints.size)
    (fun index => checkConstraint witness circuit.constraints[index]!)
    (fun index => s!"R1CS constraint {index} failed.") checked
  have lengthGuard : (witness.size != circuit.nVars) = false := by simp [shape]
  have constantGuard : (witness[0]? != some 1) = false := by simp [constant]
  unfold checkCircuit
  simp only [lengthGuard, constantGuard, fields, Bool.false_eq_true, ↓reduceIte]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [completed]
  rfl

end LeanCrypto.Proofs.R1CSModel

#print axioms LeanCrypto.Proofs.R1CSModel.row_admitted_iff
#print axioms LeanCrypto.Proofs.R1CSModel.fold_value
#print axioms LeanCrypto.Proofs.R1CSModel.rowValue_bounded
#print axioms LeanCrypto.Proofs.R1CSModel.rowValue_model
#print axioms LeanCrypto.Proofs.R1CSModel.evaluateRow_construct
#print axioms LeanCrypto.Proofs.R1CSModel.checkConstraint_construct
#print axioms LeanCrypto.Proofs.R1CSModel.checked_list_loop
#print axioms LeanCrypto.Proofs.R1CSModel.checkCircuit_construct
