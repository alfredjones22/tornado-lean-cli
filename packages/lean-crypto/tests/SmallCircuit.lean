import LeanCrypto.Groth16.R1CS
import LeanCrypto.Groth16.FFT
import LeanCrypto.Groth16.MSM
import LeanCrypto.Groth16.Verify
import LeanCrypto.Keccak

/-! Public test-only setup for x*x=y, with disclosed setup/blinding scalars.
The independent fixture uses micro-zk-proofs/noble and an O(n²) inverse DFT
plus schoolbook product for H. This is interoperability evidence, not a
production trusted setup or a universal Groth16 soundness theorem. -/

open Lean LeanCrypto LeanCrypto.BN254 LeanCrypto.Groth16 LeanCrypto.Groth16.Types

private instance : Inhabited G1.Affine := ⟨⟨G1.Fp.ofNat 1, G1.Fp.ofNat 2⟩⟩

private def checked (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def field (json : Json) (name : String) : IO Json := checked <| json.getObjVal? name
private def array (json : Json) : IO (Array Json) := checked json.getArr?

private def decimal (json : Json) : IO Nat := do
  let text ← checked json.getStr?
  let some n := text.toNat? | throw <| IO.userError "Invalid test integer."
  pure n

private def numbers (json : Json) : IO (Array Nat) := do
  (← array json).mapM decimal

private def decodedG1 (json : Json) : IO DecodedG1 := do
  if json == Json.null then return .identity
  let coordinates ← numbers json
  if coordinates.size != 3 then throw <| IO.userError "Expected three G1 coordinates."
  if coordinates[2]! == 0 then
    require (coordinates[0]! == 0 && coordinates[1]! == 1) "Noncanonical G1 identity."
    return .identity
  require (coordinates[2]! == 1) "G1 fixture is not affine."
  let _ ← checked <| G1.Affine.checked coordinates[0]! coordinates[1]!
  return .point ⟨coordinates[0]!, coordinates[1]!⟩

private def decodedG2 (json : Json) : IO DecodedG2 := do
  if json == Json.null then return .identity
  let coordinates ← array json
  if coordinates.size != 3 then throw <| IO.userError "Expected three G2 coordinates."
  let x ← numbers coordinates[0]!
  let y ← numbers coordinates[1]!
  let z ← numbers coordinates[2]!
  if x.size != 2 || y.size != 2 || z.size != 2 then
    throw <| IO.userError "Expected Fp2 coordinates."
  if z == #[0, 0] then
    require (x == #[0, 0] && y == #[1, 0]) "Noncanonical G2 identity."
    return .identity
  require (z == #[1, 0]) "G2 fixture is not affine."
  return .point (← checked <| G2.Affine.checked x[0]! x[1]! y[0]! y[1]!)

private def affineG1 (json : Json) : IO G1.Affine := do
  match ← decodedG1 json with
  | .identity => throw <| IO.userError "Proof or verification key contains G1 infinity."
  | .point point => checked <| G1.Affine.checked point.x point.y

private def affineG2 (json : Json) : IO G2.Affine := do
  match ← decodedG2 json with
  | .identity => throw <| IO.userError "Proof or verification key contains G2 infinity."
  | .point point => pure point

private def polynomial (json : Json) : IO Polynomial := do
  let row ← checked <| R1CS.decodeLinearCombination json
  return ⟨row.terms.map (fun (index, coefficient) => ⟨index, coefficient⟩)⟩

private def queryKey (json : Json) : IO QueryKey := do
  let nPublic ← checked <| (← field json "nPublic").getNat?
  let c ← (← array (← field json "C")).mapM decodedG1
  return {
    nPublic,
    vkAlpha1 := ← decodedG1 (← field json "vk_alfa_1"),
    vkBeta1 := ← decodedG1 (← field json "vk_beta_1"),
    vkDelta1 := ← decodedG1 (← field json "vk_delta_1"),
    vkBeta2 := ← decodedG2 (← field json "vk_beta_2"),
    vkDelta2 := ← decodedG2 (← field json "vk_delta_2"),
    queryA := ← (← array (← field json "A")).mapM decodedG1,
    queryB1 := ← (← array (← field json "B1")).mapM decodedG1,
    queryB2 := ← (← array (← field json "B2")).mapM decodedG2,
    queryC := c.extract (nPublic + 1) c.size,
    hExps := ← (← array (← field json "hExps")).mapM decodedG1 }

private def verificationKey (json : Json) : IO Verify.VerifyingKey := do
  return {
    alpha1 := ← affineG1 (← field json "vk_alfa_1"),
    beta2 := ← affineG2 (← field json "vk_beta_2"),
    gamma2 := ← affineG2 (← field json "vk_gamma_2"),
    delta2 := ← affineG2 (← field json "vk_delta_2"),
    ic := ← (← array (← field json "IC")).mapM affineG1 }

private def proof (json : Json) : IO Verify.Proof := do
  return {
    a := ← affineG1 (← field json "pi_a"),
    b := ← affineG2 (← field json "pi_b"),
    c := ← affineG1 (← field json "pi_c") }

private def sameG1 (actual : G1.Jacobian) (expected : G1.Affine) : IO Bool := do
  match ← checked actual.toAffine with
  | none => pure false
  | some point => pure (point.x.val == expected.x.val && point.y.val == expected.y.val)

private def sameG2 (actual : G2.Jacobian) (expected : G2.Affine) : IO Bool := do
  match ← checked actual.toAffine with
  | none => pure false
  | some point => pure (point.x == expected.x && point.y == expected.y)

def main : IO Unit := do
  let json ← checked <| Json.parse (← IO.FS.readFile "fixtures/small-circuit-vectors.json")
  let circuit ← checked <| R1CS.decodeCircuit (← field json "circuit")
  let witness ← numbers (← field json "witness")
  require (circuit.nVars == 3 && circuit.nPublic == 1 && witness == #[1,49,7])
    "The second circuit did not retain its independent dimensions."
  require ((← checked <| R1CS.checkCircuit circuit witness) == 1) "The second R1CS relation failed."
  require (!(R1CS.checkCircuit circuit (witness.set! 1 50)).isOk) "The wrong square satisfied the relation."
  let keyJson ← field json "provingKey"
  let key ← queryKey keyJson
  let pA ← (← array (← field keyJson "polsA")).mapM polynomial
  let pB ← (← array (← field keyJson "polsB")).mapM polynomial
  let h ← checked <| FFT.calculateH 4 witness pA pB
  require (h == (← numbers (← field json "h"))) "FFT H differs from independent inverse-DFT/schoolbook oracle."
  let r ← decimal (← field json "blindingR")
  let s ← decimal (← field json "blindingS")
  let points ← checked <| MSM.assemble key witness h r s
  let oracle ← proof (← field json "proof")
  require ((← sameG1 points.piA oracle.a) && (← sameG2 points.piB oracle.b) &&
    (← sameG1 points.piC oracle.c) && points.publicSignals == #[49])
    "Generic native proof points differ from the independent second-circuit oracle."
  let serialized ← checked <| MSM.solidityProofBytes points
  require ("0x" ++ bytesToHex serialized == (← checked <| (← field json "solidityProofHex").getStr?))
    "The independent proof bytes changed."
  let key ← verificationKey (← field json "verifyingKey")
  require (key.ic.size == 2) "One public input did not require exactly two IC points."
  require (← checked <| Verify.verify key oracle #[49]) "Native pairing rejected the independent public proof."
  require (!(← checked <| Verify.verify key oracle #[50])) "Native pairing accepted a changed public signal."
  require (!(Verify.publicInputPoint key #[G1.scalarPrime]).isOk) "Noncanonical scalar accepted."
  require (!(Verify.publicInputPoint key #[]).isOk) "Mismatched public dimensions accepted."
  require (!(Verify.publicInputPoint { key with ic := #[key.ic[0]!] } #[49]).isOk)
    "Missing IC point accepted."
  let zeroPublic := { key with ic := #[key.ic[0]!] }
  let _ ← checked <| Verify.publicInputPoint zeroPublic #[]
  let oversized := Array.replicate (Verify.maxPublicSignals + 1) 0
  require (!(Verify.publicInputPoint { key with ic := Array.replicate (oversized.size + 1) key.ic[0]! }
    oversized).isOk) "Generic public input resource bound ignored."
  let cancel := { key.ic[0]! with y := key.ic[0]!.y.neg }
  require (!(Verify.publicInputPoint { key with ic := #[key.ic[0]!, cancel] } #[1]).isOk)
    "Infinity public-input commitment accepted."
  require (!(MSM.solidityProofBytes { points with piA := .infinity }).isOk) "Infinity proof A serialized."
  require (!(G1.Affine.checked G1.basePrime 2).isOk) "Out-of-field G1 coordinate accepted."
  IO.println "PASS: standalone second-circuit R1CS, independent H/point/proof-byte oracle, one-input pairing acceptance, signal tamper, zero-input API, dimension/resource and canonical guards"
