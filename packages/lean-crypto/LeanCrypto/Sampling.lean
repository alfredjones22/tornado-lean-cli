import LeanCrypto.Constants
import LeanCrypto.FixedBytes

/-! Pure bounded rejection control flow and nonzero BN254 scalar admission.
No entropy source or IO implementation is provided here. -/

namespace LeanCrypto.Sampling


structure Scalar where
  value : Nat
  positive : 0 < value
  canonical : value < LeanCrypto.bn254ScalarPrime

def maxAttempts : Nat := 512

def bigEndianNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- Shared rejection decision. No witness or previously accepted scalar is
an input; the modulus and decoded candidate determine the branch. -/
def admissible (modulus value : Nat) : Bool := decide (0 < value ∧ value < modulus)

def admitValue (value : Nat) : Option Scalar :=
  if h : admissible LeanCrypto.bn254ScalarPrime value = true then
    let bounds := of_decide_eq_true h
    some ⟨value, bounds.1, bounds.2⟩
  else none

/-- The common lazy control flow used by IO, the isolated worker effect
program and the finite-distribution model. Each retry consumes one draw;
success returns immediately and exhaustion performs no additional draw. -/
def sampleLoop {m : Type → Type} [Monad m] {α : Type}
    (draw : m (Option α)) (exhausted : m α) : Nat → m α
  | 0 => exhausted
  | budget + 1 => do
    match ← draw with
    | some value => pure value
    | none => sampleLoop draw exhausted budget

def samplePairLoop {m : Type → Type} [Monad m] {α : Type}
    (draw : m (Option α)) (exhausted : m α) (budget : Nat) : m (α × α) := do
  let r ← sampleLoop draw exhausted budget
  let s ← sampleLoop draw exhausted budget
  return (r, s)

/-- A malformed entropy read is an error. Zero and values outside Fr are
    rejected for a fresh draw, without modulo reduction or modulo bias. -/
def admitCandidate (bytes : ByteArray) : Except String (Option Scalar) :=
  if bytes.size = 32 then
    .ok (admitValue (bigEndianNat bytes))
  else .error "Groth16 CSPRNG read was not exactly 32 bytes."

theorem admitted_scalar_shape (bytes : ByteArray) (scalar : Scalar)
    (h : admitCandidate bytes = .ok (some scalar)) :
    bytes.size = 32 ∧ 0 < scalar.value ∧ scalar.value < LeanCrypto.bn254ScalarPrime := by
  unfold admitCandidate at h
  by_cases hs : bytes.size = 32
  · exact ⟨hs, scalar.positive, scalar.canonical⟩
  · simp [hs] at h

end LeanCrypto.Sampling

#print axioms LeanCrypto.Sampling.admitted_scalar_shape
