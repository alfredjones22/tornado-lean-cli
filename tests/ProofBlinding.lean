import Tornado.Runtime.ProofBlinding

namespace Tornado.Runtime.ProofBlinding.Test

open Tornado.Protocol.Groth16R1CS
open Tornado.Runtime.ProofBlinding

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def word (value : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for index in [0:32] do
    bytes := bytes.push ((value / 256 ^ (31 - index) % 256).toUInt8)
  return bytes

private def someValue (result : Except String (Option Scalar)) (expected : Nat) : IO Unit :=
  match result with
  | .ok (some scalar) => require (scalar.value == expected) "Admitted the wrong scalar."
  | _ => throw <| IO.userError "Valid scalar was not admitted."

private def rejectedCandidate (bytes : ByteArray) : Bool :=
  match admitCandidate bytes with
  | .ok none => true
  | _ => false

private def malformedCandidate (bytes : ByteArray) : Bool :=
  match admitCandidate bytes with
  | .error _ => true
  | _ => false

private def rejects (action : IO α) (message : String) : IO Unit := do
  let mut didReject := false
  try
    let _ ← action
  catch _ => didReject := true
  require didReject message

def main : IO UInt32 := do
  try
    someValue (admitCandidate (word 1)) 1
    someValue (admitCandidate (word (scalarPrime - 1))) (scalarPrime - 1)
    require (rejectedCandidate (word 0))
      "Zero blinding scalar was admitted."
    require (rejectedCandidate (word scalarPrime))
      "Fr modulus was admitted."
    require (rejectedCandidate (word (2 ^ 256 - 1)))
      "Out-of-field uint256 was admitted via modulo reduction."
    require (malformedCandidate ((word 1).extract 0 31))
      "Short entropy read was accepted."
    require (malformedCandidate ((word 1).push 0))
      "Long entropy read was accepted."

    let calls ← IO.mkRef (0 : Nat)
    let twoReads : Nat → IO ByteArray := fun count => do
      require (count == 32) "Sampler did not request 32 bytes."
      let n ← calls.get
      calls.set (n + 1)
      pure (word (n + 1))
    let (r, s) ← samplePairWith twoReads
    require (r.value == 1 && s.value == 2 && (← calls.get) == 2)
      "Blinding scalars did not use separate 32-byte reads."

    let attempts ← IO.mkRef (0 : Nat)
    let retryReads : Nat → IO ByteArray := fun count => do
      require (count == 32) "Retry did not request 32 bytes."
      let n ← attempts.get
      attempts.set (n + 1)
      pure (if n == 0 then word 0 else if n == 1 then word scalarPrime else word 3)
    let admitted ← sampleScalarWith retryReads
    require (admitted.value == 3 && (← attempts.get) == 3)
      "Rejection sampling did not retry zero and out-of-field draws."

    let exhausted ← IO.mkRef (0 : Nat)
    let onlyZero : Nat → IO ByteArray := fun count => do
      require (count == 32) "Exhaustion read did not request 32 bytes."
      exhausted.modify (· + 1)
      pure (word 0)
    rejects (sampleScalarWith onlyZero) "Bounded retry exhaustion did not fail closed."
    require ((← exhausted.get) == maxAttempts)
      "Sampler exceeded its retry bound."

    let malformedReads ← IO.mkRef (0 : Nat)
    let shortRead : Nat → IO ByteArray := fun _ => do
      malformedReads.modify (· + 1)
      pure ByteArray.empty
    rejects (sampleScalarWith shortRead) "Malformed entropy read did not fail closed."
    require ((← malformedReads.get) == 1)
      "Malformed entropy was retried as if it were a valid rejection."
    let broken : Nat → IO ByteArray := fun _ =>
      throw <| IO.userError "CSPRNG failure"
    rejects (sampleScalarWith broken) "CSPRNG failure did not propagate."
    IO.println "PASS: unbiased bounded Groth16 blinding admission and injected entropy"
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)

end Tornado.Runtime.ProofBlinding.Test

def main : IO UInt32 := Tornado.Runtime.ProofBlinding.Test.main
