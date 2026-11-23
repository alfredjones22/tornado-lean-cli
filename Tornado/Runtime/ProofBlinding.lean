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

private def bigEndianNat (bytes : ByteArray) : Nat :=
  bytes.data.foldl (fun value byte => value * 256 + byte.toNat) 0

/-- A malformed entropy read is an error. Zero and values outside Fr are
    rejected for a fresh draw, without modulo reduction or modulo bias. -/
def admitCandidate (bytes : ByteArray) : Except String (Option Scalar) :=
  if bytes.size = 32 then
    let value := bigEndianNat bytes
    if h : 0 < value ∧ value < scalarPrime then
      .ok (some ⟨value, h.1, h.2⟩)
    else .ok none
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
def sampleScalarWith (read : Nat → IO ByteArray) : IO Scalar := do
  for _ in [0:maxAttempts] do
    let bytes ← read 32
    match admitCandidate bytes with
    | .error message => throw <| IO.userError message
    | .ok none => pure ()
    | .ok (some scalar) => return scalar
  throw <| IO.userError "Groth16 blinding CSPRNG exhausted its bounded retries."

/-- `r` and `s` are sampled sequentially through separate 32-byte reads.
    Independent uniform reads may coincidentally yield equal values. -/
def samplePairWith (read : Nat → IO ByteArray) : IO (Scalar × Scalar) := do
  let r ← sampleScalarWith read
  let s ← sampleScalarWith read
  return (r, s)

def samplePair : IO (Scalar × Scalar) :=
  samplePairWith Tornado.Runtime.Entropy.readKernelRandom

end Tornado.Runtime.ProofBlinding

#print axioms Tornado.Runtime.ProofBlinding.admitted_scalar_shape
