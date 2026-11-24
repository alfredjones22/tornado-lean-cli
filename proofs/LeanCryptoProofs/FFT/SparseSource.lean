import LeanCryptoProofs.FFT.NativeTransform
set_option autoImplicit false

namespace LeanCrypto.Proofs.FFT

open LeanCrypto.Groth16 LeanCrypto.Proofs.BN254Fr

abbrev Entry := Types.PolynomialEntry

def entryStep (values : Array Nat) (weight : Nat) (entry : Entry) : Array Nat :=
  values.set! entry.constraint
    (FFT.add values[entry.constraint]! (FFT.mul weight entry.coefficient))

def entryLoop (domain weight : Nat) (entries : List Entry) (input : Array Nat) :
    Except String (Array Nat) := do
  let mut values := input
  for entry in entries do
    if entry.constraint >= domain || entry.coefficient >= FFT.modulus then
      throw "Sparse polynomial entry is outside the proving domain."
    values := entryStep values weight entry
  return values

def ValidEntries (domain : Nat) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, entry.constraint < domain ∧ entry.coefficient < Q

theorem entryLoop_construct (domain weight : Nat) (entries : List Entry)
    (valid : ValidEntries domain entries) (input : Array Nat) :
    entryLoop domain weight entries input =
      .ok (entries.foldl (fun values entry => entryStep values weight entry) input) := by
  induction entries generalizing input with
  | nil => simp [entryLoop]; rfl
  | cons entry rest ih =>
    obtain ⟨rowBound, coefficientBound⟩ := valid entry (by simp)
    change entry.coefficient < FFT.modulus at coefficientBound
    have bad : (decide (entry.constraint >= domain) || decide (entry.coefficient >= FFT.modulus)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      omega
    have tailValid : ValidEntries domain rest := by
      intro value member
      exact valid value (by simp only [List.mem_cons]; exact Or.inr member)
    simp only [entryLoop, List.forIn_cons, bad, Bool.false_eq_true, ↓reduceIte,
      List.foldl_cons]
    simpa only [entryLoop] using ih tailValid (entryStep input weight entry)

def sourceEvaluations (domain : Nat) (witness : Array Nat) (polynomials : Array Types.Polynomial) : Array Nat :=
  (List.range witness.size).foldl (fun values signal =>
    polynomials[signal]!.entries.toList.foldl
      (fun values entry => entryStep values witness[signal]! entry) values) (Array.replicate domain 0)

def signalLoop (domain : Nat) (witness : Array Nat) (polynomials : Array Types.Polynomial)
    (signals : List Nat) (input : Array Nat) : Except String (Array Nat) := do
  let mut values := input
  for signal in signals do
    values ← entryLoop domain witness[signal]! polynomials[signal]!.entries.toList values
  return values

theorem signalLoop_construct (domain : Nat) (witness : Array Nat) (polynomials : Array Types.Polynomial)
    (signals : List Nat)
    (valid : ∀ signal ∈ signals, ValidEntries domain polynomials[signal]!.entries.toList)
    (input : Array Nat) :
    signalLoop domain witness polynomials signals input = .ok (signals.foldl (fun values signal =>
      polynomials[signal]!.entries.toList.foldl
        (fun values entry => entryStep values witness[signal]! entry) values) input) := by
  induction signals generalizing input with
  | nil => simp [signalLoop]; rfl
  | cons signal rest ih =>
    have head := entryLoop_construct domain witness[signal]! polynomials[signal]!.entries.toList
      (valid signal (by simp)) input
    have tail : ∀ signal ∈ rest, ValidEntries domain polynomials[signal]!.entries.toList := by
      intro value member
      exact valid value (by simp only [List.mem_cons]; exact Or.inr member)
    simp only [signalLoop, List.forIn_cons, head, List.foldl_cons]
    simpa only [signalLoop] using ih tail
      (polynomials[signal]!.entries.toList.foldl
        (fun values entry => entryStep values witness[signal]! entry) input)

theorem sumEvaluations_source (domain : Nat) (witness : Array Nat) (polynomials : Array Types.Polynomial)
    (admitted : FFT.validSize domain = true) (domainBound : domain ≤ FFT.provingDomainSize)
    (dimensions : witness.size = polynomials.size) (positive : 0 < witness.size)
    (canonical : Canonical witness)
    (valid : ∀ signal, signal < witness.size → ValidEntries domain polynomials[signal]!.entries.toList) :
    FFT.sumEvaluations domain witness polynomials = .ok (sourceEvaluations domain witness polynomials) := by
  have nonempty : witness.isEmpty = false := by simp [Array.isEmpty, Nat.ne_of_gt positive]
  have start := signalLoop_construct domain witness polynomials (List.range witness.size)
    (fun signal member => valid signal (List.mem_range.mp member)) (Array.replicate domain 0)
  have dimensionsTest : (witness.size != polynomials.size) = false := by
    exact bne_eq_false_iff_eq.mpr dimensions
  have domainGuard : (!FFT.validSize domain || decide (domain > FFT.provingDomainSize)) = false := by
    simp only [admitted, Bool.not_true, Bool.false_or, decide_eq_false_iff_not]
    omega
  have witnessGuard : (witness.size != polynomials.size || witness.isEmpty ||
      !witness.all (· < FFT.modulus)) = false := by
    simp only [dimensionsTest, nonempty, canonical_all witness canonical,
      Bool.not_true, Bool.or_self]
  rw [FFT.sumEvaluations]
  simp only [domainGuard, witnessGuard, Bool.false_eq_true, ↓reduceIte]
  change ((do
    let mut values := Array.replicate domain 0
    for signal in [0:witness.size] do
      for entry in polynomials[signal]!.entries do
        if entry.constraint >= domain || entry.coefficient >= FFT.modulus then
          throw "Sparse polynomial entry is outside the proving domain."
        values := entryStep values witness[signal]! entry
    return values) : Except String (Array Nat)) = _
  have arrayToList (signal : Nat) (values : Array Nat) :
      (do
        let mut result := values
        for entry in polynomials[signal]!.entries do
          if entry.constraint >= domain || entry.coefficient >= FFT.modulus then
            throw "Sparse polynomial entry is outside the proving domain."
          result := entryStep result witness[signal]! entry
        return result : Except String (Array Nat)) =
        entryLoop domain witness[signal]! polynomials[signal]!.entries.toList values := by
    simp only [entryLoop, Array.forIn_toList]
  simpa [signalLoop, sourceEvaluations, List.range_eq_range', entryLoop, entryStep]
    using start

end LeanCrypto.Proofs.FFT

#print axioms LeanCrypto.Proofs.FFT.entryLoop_construct
#print axioms LeanCrypto.Proofs.FFT.signalLoop_construct
#print axioms LeanCrypto.Proofs.FFT.sumEvaluations_source
