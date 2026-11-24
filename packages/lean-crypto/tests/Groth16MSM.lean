import LeanCrypto.Keccak
import Lean
import LeanCrypto.Groth16.MSM

open Lean LeanCrypto.Groth16.MSM
open LeanCrypto.BN254 LeanCrypto.Groth16
open LeanCrypto.Groth16.Types
open LeanCrypto

private def require (condition : Bool) (label : String) : Except String Unit :=
  if condition then .ok () else .error label

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def decimal (json : Json) : Except String Nat := do
  let raw ← json.getStr?
  let some value := raw.toNat? | throw "Invalid decimal test vector."
  return value

private def natField (json : Json) (name : String) : Except String Nat :=
  field json name >>= decimal

private def parseG1 (json : Json) : Except String Types.DecodedG1 := do
  if json == Json.null then return .identity
  let x ← natField json "x"
  let y ← natField json "y"
  let _ ← G1.Affine.checked x y
  return .point ⟨x, y⟩

private def parseG2 (json : Json) : Except String Types.DecodedG2 := do
  if json == Json.null then return .identity
  return .point (← G2.Affine.checked
    (← natField json "x0") (← natField json "x1")
    (← natField json "y0") (← natField json "y1"))

private def arrayOf (json : Json) (decode : Json → Except String α) :
    Except String (Array α) := do
  let items ← json.getArr?
  return (← items.toList.mapM decode).toArray

private def natArray (json : Json) : Except String (Array Nat) :=
  arrayOf json decimal

private def g1Array (json : Json) : Except String (Array Types.DecodedG1) :=
  arrayOf json parseG1

private def g2Array (json : Json) : Except String (Array Types.DecodedG2) :=
  arrayOf json parseG2

private def sameG1 (actual : G1.Jacobian) (expected : Json) :
    Except String Bool := do
  let value ← actual.toAffine
  if expected == Json.null then return value.isNone
  let some point := value | return false
  return point.x.val == (← natField expected "x") &&
    point.y.val == (← natField expected "y")

private def sameG2 (actual : G2.Jacobian) (expected : Json) :
    Except String Bool := do
  let value ← actual.toAffine
  if expected == Json.null then return value.isNone
  let some point := value | return false
  return point.x.c0.val == (← natField expected "x0") &&
    point.x.c1.val == (← natField expected "x1") &&
    point.y.c0.val == (← natField expected "y0") &&
    point.y.c1.val == (← natField expected "y1")

private def parseKey (json : Json) : Except String QueryKey := do
  return {
    nPublic := ← (← field json "nPublic").getNat?
    vkAlpha1 := ← parseG1 (← field json "vkAlpha1")
    vkBeta1 := ← parseG1 (← field json "vkBeta1")
    vkDelta1 := ← parseG1 (← field json "vkDelta1")
    vkBeta2 := ← parseG2 (← field json "vkBeta2")
    vkDelta2 := ← parseG2 (← field json "vkDelta2")
    queryA := ← g1Array (← field json "queryA")
    queryB1 := ← g1Array (← field json "queryB1")
    queryB2 := ← g2Array (← field json "queryB2")
    queryC := ← g1Array (← field json "queryC")
    hExps := ← g1Array (← field json "hExps")
  }

private def check (fixture : Json) : Except String Unit := do
  require ((← field fixture "scalarOrder") == toJson (toString order))
    "BN254 Fr order changed."
  let cases ← (← field fixture "msmCases").getArr?
  require (cases.size == 4) "Expected four MSM vectors."
  for item in cases do
    let group ← (← field item "group").getStr?
    let scalars ← natArray (← field item "scalars")
    if group == "g1" then
      let points ← g1Array (← field item "points")
      let actual ← msmG1 points scalars
      require (← sameG1 actual (← field item "result"))
        "Native G1 MSM differs from the pinned noble vector."
    else if group == "g2" then
      let points ← g2Array (← field item "points")
      let actual ← msmG2 points scalars
      require (← sameG2 actual (← field item "result"))
        "Native G2 MSM differs from the pinned noble vector."
    else throw "Unknown MSM vector group."
  let windows ← (← field fixture "windowCases").getArr?
  require (windows.size == 3) "Expected three windowed MSM vectors."
  for item in windows do
    let group ← (← field item "group").getStr?
    let count ← (← field item "count").getNat?
    let scalar ← natField item "scalar"
    let scalars := Array.replicate count scalar
    if group == "g1" then
      let point : Types.DecodedG1 := .point ⟨1, 2⟩
      let actual ← msmG1 (Array.replicate count point) scalars
      require (← sameG1 actual (← field item "result"))
        "Native windowed G1 MSM differs from noble."
    else if group == "g2" then
      let point : Types.DecodedG2 := .point G2.generator
      let actual ← msmG2 (Array.replicate count point) scalars
      require (← sameG2 actual (← field item "result"))
        "Native windowed G2 MSM differs from noble."
    else throw "Unknown windowed MSM group."
  let assembly ← field fixture "assembly"
  let key ← parseKey (← field assembly "key")
  let witness ← natArray (← field assembly "witness")
  let h ← natArray (← field assembly "h")
  let r ← natField assembly "r"
  let s ← natField assembly "s"
  let actual ← assemble key witness h r s
  let expected ← field assembly "result"
  require ((← sameG1 actual.piA (← field expected "piA")) &&
    (← sameG2 actual.piB (← field expected "piB")) &&
    (← sameG1 actual.piC (← field expected "piC")) &&
    actual.publicSignals == (← natArray (← field expected "publicSignals")))
    "Native Groth16 point formula differs from the pinned noble vector."
  let solidity ← solidityProofBytes actual
  require (solidity.size == 256 &&
    "0x" ++ bytesToHex solidity == (← (← field expected "solidityHex").getStr?))
    "Solidity proof bytes differ from the pinned SDK word order."
  require (!(solidityProofBytes { actual with piA := .infinity }).isOk)
    "A proof point at infinity was serialized."
  require (!(solidityProofBytes { actual with piB := .infinity }).isOk)
    "B proof point at infinity was serialized."
  require (!(solidityProofBytes { actual with piC := .infinity }).isOk)
    "C proof point at infinity was serialized."
  require (!(msmG1 key.queryA #[1]).isOk) "G1 mismatched counts accepted."
  require (!(msmG2 key.queryB2 #[1]).isOk) "G2 mismatched counts accepted."
  require (!(msmG1 #[key.vkAlpha1] #[order]).isOk)
    "Out-of-field G1 scalar accepted."
  require (!(msmG2 #[key.vkBeta2] #[order]).isOk)
    "Out-of-field G2 scalar accepted."
  require (!(msmG1 #[.point ⟨0, 0⟩] #[0]).isOk)
    "Off-curve G1 point hidden by zero scalar."
  let badG2 : G2.Affine :=
    ⟨G2.Fp2.zero, G2.Fp2.zero⟩
  require (!(msmG2 #[.point badG2] #[0]).isOk)
    "Off-twist G2 point hidden by zero scalar."
  require (!(assemble { key with queryC := #[] } witness h r s).isOk)
    "Wrong C-query offset accepted."
  require (!(assemble key (witness.set! 0 0) h r s).isOk)
    "Witness without constant one accepted."
  require (!(assemble key witness h order s).isOk)
    "Out-of-field blinding scalar accepted."
  require (!(assemble key witness (h.push 1) r s).isOk)
    "H polynomial longer than H-exponents accepted."

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/groth16-msm-vectors.json"
  match Json.parse raw >>= check with
  | .ok _ =>
      IO.println "PASS: 4 MSM, 3 windowed MSM, 1 Groth16/Solidity vector, and 13 rejection checks"
      return 0
  | .error error =>
      IO.eprintln error
      return 1
