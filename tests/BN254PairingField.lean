import Lean
import Tornado.Protocol.BN254PairingField

namespace Tornado.Protocol.BN254PairingField.Test

open Lean Tornado.Protocol.BN254G1 Tornado.Protocol.BN254G2
open Tornado.Protocol.BN254PairingField

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw <| IO.userError message

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw <| IO.userError message

private def field (value : Json) (name : String) : Except String Json :=
  value.getObjVal? name

private def nats (value : Json) : Except String (Array Nat) := do
  let raw ← value.getArr?
  raw.mapM fun item => do
    let text ← item.getStr?
    let some nat := text.toNat? | throw "Invalid decimal field limb."
    if nat >= basePrime then throw "Out-of-range field limb in fixture."
    return nat

private def fp2 (values : Array Nat) (index : Nat) : Fp2 :=
  Fp2.ofNats values[index]! values[index + 1]!

private def fp6 (values : Array Nat) (index : Nat := 0) : Fp6 :=
  ⟨fp2 values index, fp2 values (index + 2), fp2 values (index + 4)⟩

private def fp12 (values : Array Nat) : Fp12 :=
  ⟨fp6 values 0, fp6 values 6⟩

private def flat2 (value : Fp2) : Array Nat :=
  #[value.c0.val, value.c1.val]

private def flat6 (value : Fp6) : Array Nat :=
  flat2 value.c0 ++ flat2 value.c1 ++ flat2 value.c2

private def flat12 (value : Fp12) : Array Nat :=
  flat6 value.c0 ++ flat6 value.c1

private def vector (item : Json) (name : String) : Except String (Array Nat) := do
  nats (← field item name)

def main : IO UInt32 := do
  try
    let fixture ← unwrap <| Json.parse
      (← IO.FS.readFile "fixtures/bn254-tower-vectors.json")
    let prime ← unwrap <| (← unwrap <| field fixture "basePrime").getStr?
    require (prime == toString basePrime) "Pinned BN254 base prime changed."
    let rows ← unwrap <| (← unwrap <| field fixture "vectors").getArr?
    require (rows.size == 3) "Expected three public extension-field vectors."
    for row in rows do
      let a ← unwrap <| vector row "a"
      let b ← unwrap <| vector row "b"
      require (a.size == 12 && b.size == 12) "Wrong fixture limb count."
      let a6 := fp6 a
      let b6 := fp6 b
      let a12 := fp12 a
      let b12 := fp12 b
      require (flat6 (a6.add b6) == (← unwrap <| vector row "fp6Add"))
        "Fp6 addition differs from noble."
      require (flat6 (a6.mul b6) == (← unwrap <| vector row "fp6Mul"))
        "Fp6 multiplication differs from noble."
      let a6inverse ← unwrap a6.inverse
      require (flat6 a6inverse == (← unwrap <| vector row "fp6Inverse") &&
        a6.mul a6inverse == Fp6.one)
        "Fp6 inverse differs from noble."
      require (flat12 (a12.mul b12) == (← unwrap <| vector row "fp12Mul"))
        "Fp12 multiplication differs from noble."
      let a12inverse ← unwrap a12.inverse
      require (flat12 a12inverse == (← unwrap <| vector row "fp12Inverse") &&
        a12.mul a12inverse == Fp12.one)
        "Fp12 inverse differs from noble."
      require (flat12 (a12.pow 12345) == (← unwrap <| vector row "fp12Pow12345"))
        "Fp12 exponentiation differs from noble."
    require ((Fp6.v.mul Fp6.v).mul Fp6.v ==
      (⟨nonresidue, Fp2.zero, Fp2.zero⟩ : Fp6))
      "Fp6 tower relation v³=9+i failed."
    require (Fp12.w.mul Fp12.w == (⟨Fp6.v, Fp6.zero⟩ : Fp12))
      "Fp12 tower relation w²=v failed."
    require (!(Fp6.zero.inverse).isOk && !(Fp12.zero.inverse).isOk)
      "Zero extension-field inverse was accepted."
    IO.println "PASS: three noble Fp6/Fp12 field vectors, tower relations, and inverse guards"
    return (0 : UInt32)
  catch error =>
    IO.eprintln error.toString
    return (1 : UInt32)

end Tornado.Protocol.BN254PairingField.Test

def main : IO UInt32 := Tornado.Protocol.BN254PairingField.Test.main
