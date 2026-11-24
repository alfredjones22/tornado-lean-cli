import LeanCrypto.Groth16.Types

/-! Explicit-input BN254 Groth16 MSM and point assembly, without an artifact
loader, circuit-specific witness VM, ABI package, entropy source or runtime.
The caller supplies a valid setup, matching witness/H polynomial and blinding
scalars. This variable-time reference does not prove protocol soundness. -/

namespace LeanCrypto.Groth16.MSM

open LeanCrypto.BN254 LeanCrypto.Groth16.Types

private def uintWord (value : Nat) : Except String ByteArray := do
  if value >= 2 ^ 256 then throw "ABI uint256 is out of range."
  let mut result := ByteArray.empty
  for i in [0:32] do
    result := result.push ((value / 2 ^ (8 * (32 - 1 - i)) % 256).toUInt8)
  return result

def order : Nat := G1.scalarPrime


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

private def g1Point : DecodedG1 → Except String G1.Jacobian
  | .identity => .ok G1.Jacobian.infinity
  | .point value => do
      let checked ← G1.Affine.checked value.x value.y
      return G1.Jacobian.ofAffine checked

private def g2Point : DecodedG2 → Except String G2.Jacobian
  | .identity => .ok G2.Jacobian.infinity
  | .point value =>
      if value.onCurve then .ok (G2.Jacobian.ofAffine value)
      else .error "Groth16 G2 point is not on the twist."

/-- Checked windowed G1 MSM. Every point is decoded even for zero scalars,
    so a malformed public `DecodedG1` cannot hide behind a zero weight. -/
def msmG1 (points : Array DecodedG1) (scalars : Array Nat) :
    Except String G1.Jacobian :=
  if points.size != scalars.size then
    .error "Groth16 G1 MSM point and scalar counts differ."
  else if !scalars.all (· < order) then
    .error "Groth16 G1 MSM scalar is outside BN254 Fr."
  else do
    let mut decoded := #[]
    for point in points do decoded := decoded.push (← g1Point point)
    return windowed decoded scalars G1.Jacobian.infinity
      G1.Jacobian.add G1.Jacobian.double

/-- Checked G2 multi-scalar sum. The parser checks the twist equation, but
    this function does not prove arbitrary G2 inputs have prime subgroup order. -/
def msmG2 (points : Array DecodedG2) (scalars : Array Nat) :
    Except String G2.Jacobian :=
  if points.size != scalars.size then
    .error "Groth16 G2 MSM point and scalar counts differ."
  else if !scalars.all (· < order) then
    .error "Groth16 G2 MSM scalar is outside BN254 Fr."
  else do
    let mut decoded := #[]
    for point in points do decoded := decoded.push (← g2Point point)
    return windowed decoded scalars G2.Jacobian.infinity
      G2.Jacobian.add G2.Jacobian.double

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
  return (← uintWord a.x.val) ++ (← uintWord a.y.val) ++
    (← uintWord b.x.c1.val) ++ (← uintWord b.x.c0.val) ++
    (← uintWord b.y.c1.val) ++ (← uintWord b.y.c0.val) ++
    (← uintWord c.x.val) ++ (← uintWord c.y.val)

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

theorem msmG1_rejects_mismatched_counts (points : Array DecodedG1)
    (scalars : Array Nat) (h : points.size != scalars.size) :
    msmG1 points scalars = .error "Groth16 G1 MSM point and scalar counts differ." := by
  simp [msmG1, h]

theorem msmG2_rejects_mismatched_counts (points : Array DecodedG2)
    (scalars : Array Nat) (h : points.size != scalars.size) :
    msmG2 points scalars = .error "Groth16 G2 MSM point and scalar counts differ." := by
  simp [msmG2, h]

end LeanCrypto.Groth16.MSM

#print axioms LeanCrypto.Groth16.MSM.msmG1_rejects_mismatched_counts
#print axioms LeanCrypto.Groth16.MSM.msmG2_rejects_mismatched_counts
