import Tornado.Runtime.Entropy
import Tornado.Protocol.Groth16R1CS
import LeanCrypto.Sampling

namespace Tornado.Runtime.ProofBlinding

export LeanCrypto.Sampling (Scalar maxAttempts bigEndianNat admissible admitValue sampleLoop samplePairLoop admitCandidate admitted_scalar_shape Scalar.mk Scalar.rec Scalar.recOn Scalar.casesOn Scalar.value Scalar.positive Scalar.canonical)

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
