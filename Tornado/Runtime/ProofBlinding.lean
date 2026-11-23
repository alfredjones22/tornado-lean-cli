import Tornado.Runtime.Entropy
import Tornado.Protocol.Groth16R1CS

/-!
Bounded rejection sampling of nonzero BN254 Fr blinding scalars. Each attempt
requests a fresh 32-byte kernel CSPRNG read. This module does not make the
current variable-time, non-zeroizing prover safe for secret-bearing use.
-/

namespace Tornado.Runtime.ProofBlinding

open Tornado.Protocol.Groth16R1CS

structure Scalar where
  value : Nat
  positive : 0 < value
  canonical : value < scalarPrime

def maxAttempts : Nat := 512

def bigEndianNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- Shared rejection decision. No witness or previously accepted scalar is
an input; the modulus and decoded candidate determine the branch. -/
def admissible (modulus value : Nat) : Bool := decide (0 < value ∧ value < modulus)

def admitValue (value : Nat) : Option Scalar :=
  if h : admissible scalarPrime value = true then
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
    bytes.size = 32 ∧ 0 < scalar.value ∧ scalar.value < scalarPrime := by
  unfold admitCandidate at h
  by_cases hs : bytes.size = 32
  · exact ⟨hs, scalar.positive, scalar.canonical⟩
  · simp [hs] at h

/-- The callback makes entropy failures testable without live randomness.
    There are at most `maxAttempts` 32-byte reads, with no fallback. -/
private def drawScalarWith (read : Nat → IO ByteArray) : IO (Option Scalar) := do
  let bytes ← read 32
  match admitCandidate bytes with
  | .error message => throw <| IO.userError message
  | .ok value => pure value

def sampleScalarWith (read : Nat → IO ByteArray) : IO Scalar :=
  sampleLoop (drawScalarWith read)
    (throw <| IO.userError "Groth16 blinding CSPRNG exhausted its bounded retries.")
    maxAttempts

/-- `r` and `s` are sampled sequentially through separate 32-byte reads.
    Independent uniform reads may coincidentally yield equal values. -/
def samplePairWith (read : Nat → IO ByteArray) : IO (Scalar × Scalar) := do
  samplePairLoop (drawScalarWith read)
    (throw <| IO.userError "Groth16 blinding CSPRNG exhausted its bounded retries.")
    maxAttempts

def samplePair : IO (Scalar × Scalar) :=
  samplePairWith Tornado.Runtime.Entropy.readKernelRandom

end Tornado.Runtime.ProofBlinding

#print axioms Tornado.Runtime.ProofBlinding.admitted_scalar_shape
