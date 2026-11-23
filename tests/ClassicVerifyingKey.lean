import Lean
import Tornado.Protocol.ClassicVerifyingKey

namespace Tornado.Protocol.ClassicVerifyingKey.Test

open Lean Tornado.Protocol.ClassicVerifyingKey
open Tornado.Protocol.BN254Groth16Verify

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejected (value : Except String α) : Bool :=
  match value with
  | .error _ => true
  | .ok _ => false

private def field (value : Json) (key : String) : IO Json :=
  unwrap (value.getObjVal? key)

private def decimal (value : Json) : IO Nat := do
  let raw ← unwrap value.getStr?
  let some n := raw.toNat? | throw (IO.userError "Expected a decimal coordinate.")
  pure n

private def pair (value : Json) : IO (Nat × Nat) := do
  let items ← unwrap value.getArr?
  if items.size != 2 then throw (IO.userError "Expected two coordinates.")
  return (← decimal items[0]!, ← decimal items[1]!)

private def checkG1 (point : Tornado.Protocol.BN254G1.Affine)
    (fixture : Json) : IO Unit := do
  let (x, y) ← pair fixture
  require (point.x.val == x && point.y.val == y && point.onCurve)
    "Compiled Classic G1 key point differs from immutable fixture."

private def checkG2 (point : Tornado.Protocol.BN254G2.Affine)
    (fixture : Json) : IO Unit := do
  let items ← unwrap fixture.getArr?
  if items.size != 2 then throw (IO.userError "Expected G2 Fp2 coordinates.")
  let (x0, x1) ← pair items[0]!
  let (y0, y1) ← pair items[1]!
  require (point.x.c0.val == x0 && point.x.c1.val == x1 &&
      point.y.c0.val == y0 && point.y.c1.val == y1 && point.onCurve)
    "Compiled Classic G2 key point differs from immutable fixture."

def main : IO Unit := do
  let fixture ← unwrap <| Json.parse
    (← IO.FS.readFile "fixtures/tornado-classic-verifying-key.json")
  let fixtureCommit ← unwrap (← field fixture "sourceCommit").getStr?
  let fixtureSha ← unwrap (← field fixture "sourceSha256").getStr?
  require (sourceCommit == fixtureCommit && sourceSha256 == fixtureSha)
    "Compiled Classic source revision differs from fixture metadata."
  let key ← unwrap checkedKey
  checkG1 key.alpha1 (← field fixture "alpha1")
  checkG2 key.beta2 (← field fixture "beta2")
  checkG2 key.gamma2 (← field fixture "gamma2")
  checkG2 key.delta2 (← field fixture "delta2")
  let ic ← unwrap (← field fixture "IC").getArr?
  require (key.ic.size == 7 && ic.size == 7)
    "Classic key must have seven public-input points."
  for i in [0:7] do
    let some point := key.ic[i]?
      | throw (IO.userError "Missing compiled IC point.")
    checkG1 point ic[i]!
  let some ic0 := key.ic[0]?
    | throw (IO.userError "Missing compiled IC origin.")
  let sample : Proof := { a := key.alpha1, b := key.beta2, c := ic0 }
  let noncanonical := #[Tornado.Protocol.BN254G1.scalarPrime, 0, 0, 0, 0, 0]
  require (rejected (verifyClassic sample noncanonical))
    "Compiled Classic verifier accepted a noncanonical public signal."
  require (rejected (verifyClassic sample #[0, 0, 0, 0, 0]))
    "Compiled Classic verifier accepted a missing public signal."
  IO.println "PASS: complete compiled Classic key matches pinned source fixture; malformed public signals rejected"

end Tornado.Protocol.ClassicVerifyingKey.Test

def main : IO Unit := Tornado.Protocol.ClassicVerifyingKey.Test.main
