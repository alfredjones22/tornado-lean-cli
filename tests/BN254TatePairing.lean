import Lean
import Tornado.Protocol.BN254TatePairing

open Lean
open Tornado.Protocol.BN254G1 Tornado.Protocol.BN254G2
open Tornado.Protocol.BN254PairingField
open Tornado.Protocol.BN254TatePairing

def main : IO Unit := do
  let fixture ← match Json.parse (← IO.FS.readFile
      "fixtures/bn254-tate-vectors.json") with
    | .ok v => pure v
    | .error err => throw (IO.userError err)
  let expected (key : String) : IO (Array Nat) := do
    let .ok raw := fixture.getObjVal? key
      | throw (IO.userError s!"Missing {key} vector.")
    let .ok entries := raw.getArr?
      | throw (IO.userError s!"Malformed {key} vector.")
    entries.mapM fun entry => do
      let .ok decimal := entry.getStr?
        | throw (IO.userError "Non-string field limb.")
      let some value := decimal.toNat?
        | throw (IO.userError "Non-decimal field limb.")
      if value >= basePrime then throw (IO.userError "Out-of-range field limb.")
      pure value
  let flat2 (v : Fp2) : Array Nat := #[v.c0.val, v.c1.val]
  let flat6 (v : Fp6) : Array Nat := flat2 v.c0 ++ flat2 v.c1 ++ flat2 v.c2
  let flat12 (v : Fp12) : Array Nat := flat6 v.c0 ++ flat6 v.c1
  let p := Tornado.Protocol.BN254G1.generator
  let q := Tornado.Protocol.BN254G2.generator
  IO.println s!"embedded G1 on curve: {(embedG1 p).onCurve}"
  IO.println s!"embedded G2 on curve: {(embedG2 q).onCurve}"
  let value ← match pair p q with
    | .ok v => pure v
    | .error err => throw (IO.userError err)
  unless value != Fp12.one && value.pow scalarPrime == Fp12.one do
    throw (IO.userError "Generator pairing was trivial or outside r-torsion.")
  unless flat12 value == (← expected "generatorPairing") do
    throw (IO.userError "Reduced Tate generator vector differs from noble arithmetic oracle.")
  let p2 ← match (Tornado.Protocol.BN254G1.Jacobian.ofAffine p).scalarMul 2 |>.toAffine with
    | .ok (some v) => pure v
    | _ => throw (IO.userError "Cannot multiply G1 generator.")
  let q2 ← match (Tornado.Protocol.BN254G2.Jacobian.ofAffine q).scalarMul 2 |>.toAffine with
    | .ok (some v) => pure v
    | _ => throw (IO.userError "Cannot multiply G2 generator.")
  let valueP2 ← match pair p2 q with
    | .ok v => pure v
    | .error err => throw (IO.userError err)
  let valueQ2 ← match pair p q2 with
    | .ok v => pure v
    | .error err => throw (IO.userError err)
  unless valueP2 == value.square && valueQ2 == value.square do
    throw (IO.userError "Generator doubling bilinearity failed.")
  unless flat12 valueP2 == (← expected "doubleG1Pairing") &&
      flat12 valueQ2 == (← expected "doubleG2Pairing") do
    throw (IO.userError "Reduced Tate doubled-generator vector differs from noble arithmetic oracle.")
  let badG1 : Tornado.Protocol.BN254G1.Affine :=
    ⟨p.x, p.y.add Tornado.Protocol.BN254G1.Fp.one⟩
  let badG2 : Tornado.Protocol.BN254G2.Affine :=
    ⟨q.x, q.y.add Tornado.Protocol.BN254G2.Fp2.one⟩
  unless !badG1.onCurve && !badG2.onCurve do
    throw (IO.userError "Malformed point fixture unexpectedly on curve.")
  if (pair badG1 q).isOk || (pair p badG2).isOk then
    throw (IO.userError "Off-curve pairing input was accepted.")
  -- Noble independently finds this x=1 twist point and reports that it is
  -- not in the Fr-order subgroup. It remains on the twist in native Lean.
  let nonsubgroupCoordinates ← expected "nonSubgroupG2"
  unless nonsubgroupCoordinates.size == 4 do
    throw (IO.userError "Expected four G2 non-subgroup coordinates.")
  let nonSubgroup : Tornado.Protocol.BN254G2.Affine := ⟨
    Tornado.Protocol.BN254G2.Fp2.ofNats
      nonsubgroupCoordinates[0]! nonsubgroupCoordinates[1]!,
    Tornado.Protocol.BN254G2.Fp2.ofNats
      nonsubgroupCoordinates[2]! nonsubgroupCoordinates[3]!⟩
  unless nonSubgroup.onCurve &&
      !((Tornado.Protocol.BN254G2.Jacobian.ofAffine nonSubgroup).scalarMul scalarPrime).isInfinity do
    throw (IO.userError "Non-subgroup G2 fixture is invalid.")
  if (pair p nonSubgroup).isOk then
    throw (IO.userError "Prime-order subgroup guard accepted a non-subgroup G2 point.")
  IO.println "PASS: three noble reduced Tate vectors, prime-order output, doubling bilinearity, malformed and non-subgroup rejection"
