import Tornado.Spec.ByteEntropy
import Tornado.Spec.BlindingDistribution
import Tornado.Encoding.FixedBytes
import Tornado.Runtime.ProofBlinding
import Tornado.Protocol.Groth16R1CS

/-! Public synthetic inputs only. No OS entropy, network, keys, or funds. -/
open Tornado.Encoding.FixedBytes
open Tornado.Spec.ByteEntropy
open Tornado.Runtime.ProofBlinding
open Tornado.Spec.BlindingDistribution
open Tornado.Protocol.Groth16R1CS

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw <| IO.userError message

/-- Independent positional-arithmetic reference; the proved encoder uses
recursive quotient/remainder splitting instead. -/
private def referenceBytes (width value : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for index in [0:width] do
    out := out.push ((value / 256 ^ (width - 1 - index) % 256).toUInt8)
  return out

private def checkWord (width value : Nat) : IO Unit := do
  let bytes := encode width value
  require (bytes.size == width && bytes == referenceBytes width value)
    "Encoder changed full-width big-endian positional bytes."
  require (decode bytes == value && bigEndianNat bytes == value)
    "Proved decoder or runtime fold failed to recover a bounded value."
  require (encode width (decode bytes) == bytes)
    "Leading zero bytes were lost during the round trip."

private def erasedCandidate (bytes : ByteArray) : Except String (Option Nat) :=
  (admitCandidate bytes).map (fun result => result.map (fun scalar => scalar.value))

private def hasCandidate (bytes : ByteArray) (expected : Option Nat) : Bool :=
  match erasedCandidate bytes with
  | .ok actual => actual == expected
  | .error _ => false

def main : IO UInt32 := do
  let domain := 2 ^ 256
  for value in [0, 1, 255, 256, 257, scalarPrime - 1, scalarPrime, domain - 1] do
    checkWord 32 value
  checkWord 0 0
  require (encode 32 0 == ByteArray.mk (Array.replicate 32 0) &&
    encode 32 (domain - 1) == ByteArray.mk (Array.replicate 32 255))
    "Zero/max uint256 encodings changed."
  require (bigEndianNat (ByteArray.mk #[1, 2]) == 258 &&
    bigEndianNat (ByteArray.mk #[1, 2]) != 513)
    "Big-endian ordering was replaced by little-endian ordering."
  require (hasCandidate (encode 32 0) none &&
    hasCandidate (encode 32 1) (some 1) &&
    hasCandidate (encode 32 (scalarPrime - 1)) (some (scalarPrime - 1)) &&
    hasCandidate (encode 32 scalarPrime) none &&
    hasCandidate (encode 32 (domain - 1)) none)
    "Runtime nonzero Fr rejection decision no longer matches decoded bytes."
  for width in [0, 1, 31, 33, 64] do
    require (!(admitCandidate (encode width 1)).isOk)
      "Malformed-width entropy reached the scalar classifier."
  -- Deterministic public synthetic pseudo-random values span the full uint256
  -- range; this is test data generation, not a claim about secure randomness.
  let mut publicState := 0x54a7d0c39b8e1f21
  for _ in [0:128] do
    publicState := (publicState * 6364136223846793005 + 1442695040888963407) % domain
    checkWord 32 publicState
  let mut histogram := Array.replicate 65536 0
  for high in [0:256] do
    for low in [0:256] do
      let bytes := ByteArray.mk #[high.toUInt8, low.toUInt8]
      let value := bigEndianNat bytes
      require (value == high * 256 + low && encode 2 value == bytes)
        "Exhaustive two-byte product did not match positional arithmetic."
      histogram := histogram.modify value (· + 1)
  require (histogram.all (· == 1))
    "The actual two-byte decoder alphabet has a missing or duplicated integer."
  require (sumBytes 0 (fun _ => 1) == 1 && sumBytes 1 (fun _ => 1) == 256 &&
    sumBytes 2 (fun _ => 1) == 65536)
    "Uniform byte-source product has incorrect cardinality."
  for value in [0, 1, 255, 256, 65535, 65536] do
    let count := sumBytes 2 (fun bytes => if bigEndianNat bytes == value then 1 else 0)
    require (count == if value < 65536 then 1 else 0)
      "Source-byte weighted counts do not transfer to uniform decoded values."
  -- An explicit lossy map on actual uniform source bytes must exhibit bias.
  let reduced := fun value => sumBytes 1
    (fun bytes => if bigEndianNat bytes % 5 == value then 1 else 0)
  require (reduced 0 == 52 && reduced 1 == 51)
    "Modulo-reduction negative control failed to expose biased output."
  let collapsed := fun value => sumBytes 1
    (fun bytes => if bigEndianNat bytes % 255 == value then 1 else 0)
  require (collapsed 0 == 2 && collapsed 255 == 0)
    "Non-bijective decoder negative control retained fictional uniform weights."
  for value in [0, 1, 2, 3, 4, 5, 255] do
    require (byteMass 1 5 2 (valueEvent value) == mass 256 5 2 (valueEvent value))
      "Byte-driven shared sampler differs from the proved decoded-value counts."
  require (byteMass 1 5 2 successEvent == 2032 &&
    byteMass 1 5 2 failureEvent == 63504)
    "Byte-driven rejection sampler success/exhaustion counts changed."
  IO.println "PASS: fixed-width uint256 runtime bridge, public synthetic round trips, exhaustive two-byte bijection, byte-source sampler counts, malformed-width rejection, and biased-map negative controls"
  return 0
