import LeanCryptoProofs.FFT.SparseSource
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

noncomputable def entryRow (entries : List Entry) (row : Nat) : Fr :=
  (entries.map (fun entry => if entry.constraint = row then model entry.coefficient else 0)).sum

noncomputable def sparseRow (witness : Array Nat) (polynomials : Array Types.Polynomial) (row : Nat) : Fr :=
  ∑ signal ∈ Finset.range witness.size,
    model witness[signal]! * entryRow polynomials[signal]!.entries.toList row

theorem entryStep_size (values : Array Nat) (weight : Nat) (entry : Entry) :
    (entryStep values weight entry).size = values.size := by simp only [entryStep, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem entryStep_canonical (values : Array Nat) (weight : Nat) (entry : Entry)
    (canonical : Canonical values) : Canonical (entryStep values weight entry) := by
  intro row bounded
  have originalBound : row < values.size := by simpa only [entryStep_size] using bounded
  simp only [entryStep, Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds originalBound]
  split
  · exact Nat.mod_lt _ (by decide)
  · exact canonical row originalBound

theorem entryStep_model (values : Array Nat) (weight : Nat) (entry : Entry)
    (row : Nat) (bounded : row < values.size) :
    fieldInput (entryStep values weight entry) row = fieldInput values row +
      model weight * (if entry.constraint = row then model entry.coefficient else 0) := by
  unfold fieldInput
  rw [getElem!_pos (entryStep values weight entry) row (by rw [entryStep_size]; exact bounded),
    getElem!_pos values row bounded]
  simp only [entryStep, Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds bounded]
  split
  · rename_i equal
    rw [equal, getElem!_pos values row bounded, model_add, model_mul]
  · simp only [mul_zero, add_zero]

theorem entriesFold_spec (values : Array Nat) (weight : Nat) (entries : List Entry)
    (canonical : Canonical values) :
    (entries.foldl (fun values entry => entryStep values weight entry) values).size = values.size ∧
    Canonical (entries.foldl (fun values entry => entryStep values weight entry) values) ∧
    ∀ row, row < values.size →
      fieldInput (entries.foldl (fun values entry => entryStep values weight entry) values) row =
        fieldInput values row + model weight * entryRow entries row := by
  induction entries generalizing values with
  | nil => simp [entryRow]; exact canonical
  | cons entry rest ih =>
    obtain ⟨size, bounded, fields⟩ := ih (entryStep values weight entry) (entryStep_canonical values weight entry canonical)
    refine ⟨size.trans (entryStep_size values weight entry), bounded, ?_⟩
    intro row rowBound
    rw [List.foldl_cons, fields row (by rw [entryStep_size]; exact rowBound), entryStep_model values weight entry row rowBound]
    simp only [entryRow, List.map_cons, List.sum_cons]
    ring

def signalPrefix (domain : Nat) (witness : Array Nat) (polynomials : Array Types.Polynomial) (length : Nat) : Array Nat :=
  (List.range length).foldl (fun values signal =>
    polynomials[signal]!.entries.toList.foldl
      (fun values entry => entryStep values witness[signal]! entry) values) (Array.replicate domain 0)

theorem signalPrefix_spec (domain : Nat) (witness : Array Nat) (polynomials : Array Types.Polynomial) (length : Nat) :
    (signalPrefix domain witness polynomials length).size = domain ∧
    Canonical (signalPrefix domain witness polynomials length) ∧
    ∀ row, row < domain →
      fieldInput (signalPrefix domain witness polynomials length) row =
        ∑ signal ∈ Finset.range length,
          model witness[signal]! * entryRow polynomials[signal]!.entries.toList row := by
  induction length with
  | zero =>
    simp only [signalPrefix, List.range_zero, List.foldl_nil, Array.size_replicate, Finset.range_zero, Finset.sum_empty]
    refine ⟨True.intro, ?_, ?_⟩
    · intro row bounded
      simp only [Array.getElem_replicate]
      exact (by decide : 0 < Q)
    · intro row bounded
      simp only [fieldInput, getElem!_pos (Array.replicate domain 0) row (by simpa), Array.getElem_replicate]
      rfl
  | succ length ih =>
    obtain ⟨size, canonical, values⟩ := ih
    have step : signalPrefix domain witness polynomials (length + 1) =
        polynomials[length]!.entries.toList.foldl
          (fun values entry => entryStep values witness[length]! entry)
          (signalPrefix domain witness polynomials length) := by
      simp only [signalPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [step]
    obtain ⟨nextSize, nextCanonical, fields⟩ := entriesFold_spec (signalPrefix domain witness polynomials length)
      witness[length]! polynomials[length]!.entries.toList canonical
    refine ⟨nextSize.trans size, nextCanonical, ?_⟩
    intro row bounded
    rw [fields row (by rw [size]; exact bounded), values row bounded, Finset.sum_range_succ]

/-- The actual checked sparse accumulator constructs the independent
signal-weighted row sums. All original signal and entry indices are retained. -/
theorem sumEvaluations_construct (domain : Nat) (witness : Array Nat) (polynomials : Array Types.Polynomial)
    (admitted : FFT.validSize domain = true) (domainBound : domain ≤ FFT.provingDomainSize)
    (dimensions : witness.size = polynomials.size) (positive : 0 < witness.size)
    (canonical : Canonical witness)
    (valid : ∀ signal, signal < witness.size → ValidEntries domain polynomials[signal]!.entries.toList) :
    ∃ output, FFT.sumEvaluations domain witness polynomials = .ok output ∧
      output.size = domain ∧ Canonical output ∧
      ∀ row, row < domain → fieldInput output row = sparseRow witness polynomials row := by
  refine ⟨sourceEvaluations domain witness polynomials,
    sumEvaluations_source domain witness polynomials admitted domainBound dimensions positive canonical valid, ?_⟩
  exact signalPrefix_spec domain witness polynomials witness.size

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.entryStep_size
#print axioms LeanCrypto.Proofs.FFT.entryStep_canonical
#print axioms LeanCrypto.Proofs.FFT.entryStep_model
#print axioms LeanCrypto.Proofs.FFT.entriesFold_spec
#print axioms LeanCrypto.Proofs.FFT.signalPrefix_spec
#print axioms LeanCrypto.Proofs.FFT.sumEvaluations_construct
