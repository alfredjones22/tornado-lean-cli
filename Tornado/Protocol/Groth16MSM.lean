import Lean
import Tornado.Protocol.BN254G1
import Tornado.Protocol.BN254G2
import Tornado.Protocol.ProvingKey
import Tornado.Protocol.FrFFT
import Tornado.Protocol.WitnessVM
import Tornado.Protocol.Abi

/-!
Pure point arithmetic for the pinned Groth16 proof equation. This module
serializes proof points to the Classic verifier's eight-word format, but
neither samples blinding randomness nor verifies a proof.
`assemble` accepts already checked field scalars and explicit blinding values.
The point operations are variable-time; this must not process funded secrets.
-/

namespace Tornado.Protocol.Groth16MSM

open Tornado.Protocol

def order : Nat := BN254G1.scalarPrime

instance : Inhabited ProvingKey.DecodedG2 := ⟨.identity⟩
instance : Inhabited BN254G1.Jacobian := ⟨.infinity⟩
instance : Inhabited BN254G2.Jacobian := ⟨.infinity⟩

private def windowBits (count : Nat) : Nat :=
  if count >= 2048 then 10 else if count >= 64 then 6 else 4

/-- Windowed bucket sum, with high windows processed first. Accumulating
    buckets from high digit to low gives each bucket its digit's multiplicity.
    All point decoding and scalar bounds are checked by the callers. -/
private def windowed [Inhabited α] (points : Array α) (scalars : Array Nat)
    (zero : α) (add : α → α → α) (double : α → α) : α := Id.run do
  let bits := windowBits points.size
  let radix := 2 ^ bits
  let windows := (254 + bits - 1) / bits
  let mut result := zero
  for w in [0:windows] do
    for _ in [0:bits] do result := double result
    let shift := (windows - 1 - w) * bits
    let divisor := 2 ^ shift
    let mut buckets := Array.replicate radix zero
    for i in [0:points.size] do
      let digit := scalars[i]! / divisor % radix
      if digit != 0 then
        buckets := buckets.set! digit (add buckets[digit]! points[i]!)
    let mut running := zero
    for d in [1:radix] do
      let digit := radix - d
      running := add running buckets[digit]!
      result := add result running
  return result

private def g1Point : ProvingKey.DecodedG1 → Except String BN254G1.Jacobian
  | .identity => .ok BN254G1.Jacobian.infinity
  | .point value => do
      let checked ← BN254G1.Affine.checked value.x value.y
      return BN254G1.Jacobian.ofAffine checked

private def g2Point : ProvingKey.DecodedG2 → Except String BN254G2.Jacobian
  | .identity => .ok BN254G2.Jacobian.infinity
  | .point value =>
      if value.onCurve then .ok (BN254G2.Jacobian.ofAffine value)
      else .error "Groth16 G2 point is not on the twist."

/-- Checked windowed G1 MSM. Every point is decoded even for zero scalars,
    so a malformed public `DecodedG1` cannot hide behind a zero weight. -/
def msmG1 (points : Array ProvingKey.DecodedG1) (scalars : Array Nat) :
    Except String BN254G1.Jacobian :=
  if points.size != scalars.size then
    .error "Groth16 G1 MSM point and scalar counts differ."
  else if !scalars.all (· < order) then
    .error "Groth16 G1 MSM scalar is outside BN254 Fr."
  else do
    let mut decoded := #[]
    for point in points do decoded := decoded.push (← g1Point point)
    return windowed decoded scalars BN254G1.Jacobian.infinity
      BN254G1.Jacobian.add BN254G1.Jacobian.double

/-- Checked G2 multi-scalar sum. The parser checks the twist equation, but
    this function does not prove arbitrary G2 inputs have prime subgroup order. -/
def msmG2 (points : Array ProvingKey.DecodedG2) (scalars : Array Nat) :
    Except String BN254G2.Jacobian :=
  if points.size != scalars.size then
    .error "Groth16 G2 MSM point and scalar counts differ."
  else if !scalars.all (· < order) then
    .error "Groth16 G2 MSM scalar is outside BN254 Fr."
  else do
    let mut decoded := #[]
    for point in points do decoded := decoded.push (← g2Point point)
    return windowed decoded scalars BN254G2.Jacobian.infinity
      BN254G2.Jacobian.add BN254G2.Jacobian.double

/-- The query arrays and fixed verification-key points needed for the proof
    equation. `queryC` omits the first `nPublic + 1` public-signal identities,
    exactly like the pinned binary key. -/
structure QueryKey where
  nPublic : Nat
  vkAlpha1 : ProvingKey.DecodedG1
  vkBeta1 : ProvingKey.DecodedG1
  vkDelta1 : ProvingKey.DecodedG1
  vkBeta2 : ProvingKey.DecodedG2
  vkDelta2 : ProvingKey.DecodedG2
  queryA : Array ProvingKey.DecodedG1
  queryB1 : Array ProvingKey.DecodedG1
  queryB2 : Array ProvingKey.DecodedG2
  queryC : Array ProvingKey.DecodedG1
  hExps : Array ProvingKey.DecodedG1

def QueryKey.fromParsed (key : ProvingKey.ParsedKey) : QueryKey :=
  ⟨key.header.nPublic, key.vkAlpha1, key.vkBeta1, key.vkDelta1,
    key.vkBeta2, key.vkDelta2, key.queryA, key.queryB1, key.queryB2,
    key.queryC, key.hExps⟩

structure ProofPoints where
  piA : BN254G1.Jacobian
  piB : BN254G2.Jacobian
  piC : BN254G1.Jacobian
  publicSignals : Array Nat

/-- The Classic Solidity verifier expects eight 32-byte big-endian words.
    BN254 G2's Fp2 limbs are reversed relative to the proving-key parser:
    `x.c1, x.c0, y.c1, y.c0`. A, B, or C at infinity is rejected. -/
def solidityProofBytes (proof : ProofPoints) : Except String ByteArray := do
  let some a ← proof.piA.toAffine
    | throw "Groth16 A proof point is at infinity."
  let some b ← proof.piB.toAffine
    | throw "Groth16 B proof point is at infinity."
  let some c ← proof.piC.toAffine
    | throw "Groth16 C proof point is at infinity."
  return (← Abi.uintWord a.x.val) ++ (← Abi.uintWord a.y.val) ++
    (← Abi.uintWord b.x.c1.val) ++ (← Abi.uintWord b.x.c0.val) ++
    (← Abi.uintWord b.y.c1.val) ++ (← Abi.uintWord b.y.c0.val) ++
    (← Abi.uintWord c.x.val) ++ (← Abi.uintWord c.y.val)

/-- Pure implementation of `micro-zk-proofs@0.3.1`'s Groth16 point formula.
    The caller must obtain `h` from the same witness and authenticated key,
    sample `r` and `s` securely and verify the resulting proof. -/
def assemble (key : QueryKey) (witness h : Array Nat) (r s : Nat) :
    Except String ProofPoints := do
  let offset := key.nPublic + 1
  if witness.isEmpty || witness[0]? != some 1 || offset > witness.size ||
      key.queryA.size != witness.size ||
      key.queryB1.size != witness.size ||
      key.queryB2.size != witness.size ||
      key.queryC.size != witness.size - offset ||
      h.size > key.hExps.size then
    throw "Groth16 proof query and witness dimensions differ."
  if r >= order || s >= order || !witness.all (· < order) ||
      !h.all (· < order) then
    throw "Groth16 proof scalar is outside BN254 Fr."
  let aWitness ← msmG1 key.queryA witness
  let a := (aWitness.add (← g1Point key.vkAlpha1)).add
    ((← g1Point key.vkDelta1).scalarMul r)
  let bWitness ← msmG2 key.queryB2 witness
  let b := (bWitness.add (← g2Point key.vkBeta2)).add
    ((← g2Point key.vkDelta2).scalarMul s)
  let b1Witness ← msmG1 key.queryB1 witness
  let b1 := (b1Witness.add (← g1Point key.vkBeta1)).add
    ((← g1Point key.vkDelta1).scalarMul s)
  let cWitness ← msmG1 key.queryC (witness.extract offset witness.size)
  let hWitness ← msmG1 (key.hExps.extract 0 h.size) h
  let minusRS := (order - (r * s % order)) % order
  let c := ((((cWitness.add hWitness).add (a.scalarMul s)).add
    (b1.scalarMul r)).add ((← g1Point key.vkDelta1).scalarMul minusRS))
  return ⟨a, b, c, witness.extract 1 offset⟩

/-- The pinned binary parser already authenticates the complete key, but
    `ParsedKey` itself is a public structure. This adapter checks its pinned
    dimensions again; it does not establish provenance unless the caller
    obtains the value from `decodeFullKey`. -/
def assembleParsed (key : ProvingKey.ParsedKey) (witness h : Array Nat)
    (r s : Nat) : Except String ProofPoints := do
  if key.header.nVars != 28300 || key.header.nPublic != 6 ||
      key.header.domainSize != 32768 || key.hExps.size != 32767 then
    throw "Groth16 parsed key does not have the pinned Tornado dimensions."
  assemble (QueryKey.fromParsed key) witness h r s

/-- The private constructor records the exact native R1CS check for the
    witness used to compute these proof points. It does not certify the
    elliptic-curve protocol equation or recipient/chain state. -/
structure CheckedProofPoints (circuit : WitnessVM.PinnedCircuit) where
  private mk ::
  witness : Array Nat
  points : ProofPoints
  checked : Groth16R1CS.checkCircuit circuit.circuit witness = .ok 28275

/-- Pure, authenticated-artifact route from the pinned Circom input to proof
    points. Blinding scalars are explicit to keep randomness outside this
    function. Its full 28,300-signal output matches a pinned SDK oracle for
    one public fixture, but the formula is not formally proven correct and
    this route must not process funded-note secrets. -/
def deriveCheckedProofPoints (key : ProvingKey.PinnedKey)
    (graph : WitnessVM.PinnedGraph) (circuit : WitnessVM.PinnedCircuit)
    (inputs : Array Nat) (commitment r s : Nat) :
    Except String (CheckedProofPoints circuit) :=
  match hw : WitnessVM.generateCheckedWitness graph circuit inputs commitment with
  | .error message => .error message
  | .ok witness => do
      let decoded ← ProvingKey.decodeFullKey key
      let h ← FrFFT.calculateH decoded.header.domainSize witness
        decoded.polsA decoded.polsB
      let points ← assembleParsed decoded witness h r s
      return ⟨witness, points,
        WitnessVM.generateCheckedWitness_passes graph circuit inputs commitment witness hw⟩

theorem derived_points_use_checked_witness (circuit : WitnessVM.PinnedCircuit)
    (result : CheckedProofPoints circuit) :
    Groth16R1CS.checkCircuit circuit.circuit result.witness = .ok 28275 :=
  result.checked

theorem msmG1_rejects_mismatched_counts (points : Array ProvingKey.DecodedG1)
    (scalars : Array Nat) (h : points.size != scalars.size) :
    msmG1 points scalars = .error "Groth16 G1 MSM point and scalar counts differ." := by
  simp [msmG1, h]

theorem msmG2_rejects_mismatched_counts (points : Array ProvingKey.DecodedG2)
    (scalars : Array Nat) (h : points.size != scalars.size) :
    msmG2 points scalars = .error "Groth16 G2 MSM point and scalar counts differ." := by
  simp [msmG2, h]

end Tornado.Protocol.Groth16MSM

#print axioms Tornado.Protocol.Groth16MSM.msmG1_rejects_mismatched_counts
#print axioms Tornado.Protocol.Groth16MSM.msmG2_rejects_mismatched_counts
#print axioms Tornado.Protocol.Groth16MSM.derived_points_use_checked_witness
