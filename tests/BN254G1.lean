import Lean
import Tornado.Protocol.BN254G1

open Lean Tornado.Protocol.BN254G1

private def value (json : Json) (field : String) : Except String Json :=
  json.getObjVal? field

private def natural (json : Json) : Except String Nat := do
  let text ← json.getStr?
  let some n := text.toNat? | throw "Invalid BN254 vector integer."
  return n

private def expectedPoint (json : Json) (actual : Option Affine) : Except String Unit := do
  match json, actual with
  | .null, none => pure ()
  | .null, some _ => throw "Expected G1 infinity."
  | _, none => throw "Unexpected G1 infinity."
  | _, some point =>
    let x ← natural (← value json "x")
    let y ← natural (← value json "y")
    if point.x.val != x || point.y.val != y then
      throw "Native BN254 G1 point differs from pinned noble vector."

private def check (root : Json) : Except String Nat := do
  if (← natural (← value root "scalarOrder")) != scalarPrime ||
      (← natural (← value root "basePrime")) != basePrime then
    throw "BN254 field parameters differ from pinned noble."
  if !generator.onCurve then throw "Native BN254 G1 generator is off curve."
  if (Affine.checked 1 3).isOk || (Affine.checked basePrime 2).isOk then
    throw "Invalid G1 coordinate was accepted."
  if (Fp.zero.inverse).isOk then throw "Zero Fp inverse was accepted."
  let inverse ← (Fp.ofNat 17).inverse
  if (Fp.ofNat 17).mul inverse != Fp.one then throw "Fp inverse check failed."
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
  return count

def main : IO UInt32 := do
  let raw ← IO.FS.readFile "fixtures/bn254-g1-vectors.json"
  match Json.parse raw >>= check with
  | .error error => IO.eprintln error; return 1
  | .ok count =>
    if count != 14 then IO.eprintln "Unexpected G1 vector count"; return 1
    IO.println "PASS: 14 pinned BN254 G1 scalar and addition vectors; field and point rejections"
    return 0
