import Lean
import LeanCrypto.BN254.G2

open Lean LeanCrypto.BN254.G2

private def value (json : Json) (field : String) : Except String Json :=
  json.getObjVal? field

private def natural (json : Json) : Except String Nat := do
  let text ← json.getStr?
  let some n := text.toNat? | throw "Invalid BN254 G2 vector integer."
  return n

private def expectedPoint (json : Json) (actual : Option Affine) : Except String Unit := do
  match json, actual with
  | .null, none => pure ()
  | .null, some _ => throw "Expected G2 infinity."
  | _, none => throw "Unexpected G2 infinity."
  | _, some point =>
    let x0 ← natural (← value json "x0")
    let x1 ← natural (← value json "x1")
    let y0 ← natural (← value json "y0")
    let y1 ← natural (← value json "y1")
    if point.x.c0.val != x0 || point.x.c1.val != x1 ||
        point.y.c0.val != y0 || point.y.c1.val != y1 then
      throw "Native BN254 G2 point differs from pinned noble vector."

private def check (root : Json) : Except String Nat := do
  if (← natural (← value root "scalarOrder")) != LeanCrypto.BN254.G1.scalarPrime ||
      (← natural (← value root "basePrime")) != LeanCrypto.BN254.G1.basePrime then
    throw "BN254 G2 field parameters differ from pinned noble."
  if !generator.onCurve then throw "Native BN254 G2 generator is off twist."
  if (Affine.checked 1 0 2 0).isOk ||
      (Affine.checked LeanCrypto.BN254.G1.basePrime 0 0 0).isOk then
    throw "Invalid G2 coordinate was accepted."
  if (Fp2.zero.inverse).isOk then throw "Zero Fp2 inverse was accepted."
  let inverse ← (Fp2.ofNats 3 4).inverse
  if (Fp2.ofNats 3 4).mul inverse != Fp2.one then
    throw "Fp2 inverse check failed."
  let mut count := 0
  let scalars ← (← value root "scalars").getArr?
  for row in scalars do
    let scalar ← natural (← value row "scalar")
    let actual ← (Jacobian.ofAffine generator).scalarMul scalar |>.toAffine
    expectedPoint (← value row "result") actual
    count := count + 1
  let additions ← (← value root "additions").getArr?
  for row in additions do
    let left ← natural (← value row "left")
    let right ← natural (← value row "right")
    let actual ← ((Jacobian.ofAffine generator).scalarMul left).add
      ((Jacobian.ofAffine generator).scalarMul right) |>.toAffine
    expectedPoint (← value row "result") actual
    count := count + 1
  if !((Jacobian.ofAffine generator).scalarMul LeanCrypto.BN254.G1.scalarPrime).isInfinity then
    throw "Pinned G2 generator did not have the expected scalar order."
  return count

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/bn254-g2-vectors.json"
  match Json.parse raw >>= check with
  | .error error => IO.eprintln error; return 1
  | .ok count =>
    if count != 14 then IO.eprintln "Unexpected G2 vector count"; return 1
    IO.println "PASS: 14 pinned BN254 G2 scalar and addition vectors; twist and field rejections"
    return 0
