import Lean
import Tornado.Protocol.BN254Groth16Verify

namespace Tornado.Protocol.BN254Groth16Verify.Test

open Lean Tornado.Protocol.BN254G1 Tornado.Protocol.BN254G2
open Tornado.Protocol.BN254Groth16Verify

private def unwrap (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error err => throw (IO.userError err)

private def field (value : Json) (key : String) : IO Json :=
  unwrap (value.getObjVal? key)

private def decimal (value : Json) : IO Nat := do
  let raw ← unwrap value.getStr?
  let some n := raw.toNat? | throw (IO.userError "Expected decimal integer.")
  pure n

private def pair (value : Json) : IO (Nat × Nat) := do
  let raw ← unwrap value.getArr?
  if raw.size != 2 then throw (IO.userError "Expected two coordinates.")
  return (← decimal raw[0]!, ← decimal raw[1]!)

private def g1 (value : Json) : IO Tornado.Protocol.BN254G1.Affine := do
  let (x,y) ← pair value
  unwrap <| Tornado.Protocol.BN254G1.Affine.checked x y

private def g2 (value : Json) : IO Tornado.Protocol.BN254G2.Affine := do
  let raw ← unwrap value.getArr?
  if raw.size != 2 then throw (IO.userError "Expected two Fp2 coordinates.")
  let (x0,x1) ← pair raw[0]!
  let (y0,y1) ← pair raw[1]!
  unwrap <| Tornado.Protocol.BN254G2.Affine.checked x0 x1 y0 y1

private def nibble (byte : UInt8) : Option Nat :=
  let n := byte.toNat
  if n >= 48 && n <= 57 then some (n - 48)
  else if n >= 97 && n <= 102 then some (n - 87)
  else if n >= 65 && n <= 70 then some (n - 55)
  else none

private def proofWords (hex : String) : Except String (Array Nat) := do
  let bytes := hex.toUTF8
  if bytes.size != 514 || bytes[0]! != 48 || bytes[1]! != 120 then
    throw "Expected eight 32-byte 0x-prefixed Solidity proof words."
  let mut result := #[]
  for i in [0:8] do
    let mut value := 0
    for j in [0:64] do
      let some digit := nibble bytes[2 + i * 64 + j]!
        | throw "Invalid hexadecimal proof word."
      value := value * 16 + digit
    result := result.push value
  return result

private def readJson (path : String) : IO Json :=
  (IO.FS.readFile path) >>= fun content => unwrap (Json.parse content)

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def expectError (message : String) (value : Except String α) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

def main : IO UInt32 := do
  try
    let started ← IO.monoMsNow
    let root := "fixtures"
    let keyJson ← readJson s!"{root}/tornado-classic-verifying-key.json"
    let proofJson ← readJson "fixtures/groth16-full-public-proof.json"
    let equationJson ← readJson s!"{root}/tornado-classic-proof-equation.json"
    let icRaw ← unwrap (← field keyJson "IC").getArr?
    let key : VerifyingKey := {
      alpha1 := ← g1 (← field keyJson "alpha1")
      beta2 := ← g2 (← field keyJson "beta2")
      gamma2 := ← g2 (← field keyJson "gamma2")
      delta2 := ← g2 (← field keyJson "delta2")
      ic := ← icRaw.mapM g1
    }
    let hex ← unwrap (← field proofJson "solidityProofHex").getStr?
    let words ← unwrap (proofWords hex)
    require (words.size == 8) "Wrong Classic proof word count."
    let proof : Proof := {
      a := ← unwrap <| Tornado.Protocol.BN254G1.Affine.checked words[0]! words[1]!
      b := ← unwrap <| Tornado.Protocol.BN254G2.Affine.checked
        words[3]! words[2]! words[5]! words[4]!
      c := ← unwrap <| Tornado.Protocol.BN254G1.Affine.checked words[6]! words[7]!
    }
    let rawSignals ← unwrap (← field proofJson "publicSignals").getArr?
    let signals ← rawSignals.mapM decimal
    let checkVkX := fun (actual : Tornado.Protocol.BN254G1.Affine) (expected : Json) => do
      let point ← g1 expected
      require (actual.x.val == point.x.val && actual.y.val == point.y.val)
        "Native public-input commitment differs from noble."
    checkVkX (← unwrap <| publicInputPoint key signals) (← field equationJson "vkX")
    require (← unwrap <| verify key proof signals)
      "Native Tate proof equation rejected the pinned valid Classic proof."
    let tamperedVkXs ← unwrap (← field equationJson "tamperedVkXBySignal").getArr?
    require (tamperedVkXs.size == 6 && signals.size == 6)
      "Expected six independent public-signal tamper oracle points."
    for i in [0:6] do
      let changed := signals.set! i (signals[i]! + 1)
      checkVkX (← unwrap <| publicInputPoint key changed) tamperedVkXs[i]!
      require (!(← unwrap <| verify key proof changed))
        s!"Native Tate proof equation accepted changed public signal {i}."
    expectError "Noncanonical public signal was accepted."
      (publicInputPoint key (signals.set! 0 scalarPrime))
    expectError "Missing public signal was accepted."
      (publicInputPoint key (signals.extract 0 5))
    expectError "Missing IC point was accepted."
      (publicInputPoint { key with ic := key.ic.extract 0 6 } signals)
    let badA : Tornado.Protocol.BN254G1.Affine :=
      ⟨proof.a.x, proof.a.y.add Tornado.Protocol.BN254G1.Fp.one⟩
    require (!badA.onCurve) "Malformed A test point unexpectedly on curve."
    expectError "Off-curve proof A was accepted."
      (verify key { proof with a := badA } signals)
    let badB : Tornado.Protocol.BN254G2.Affine :=
      ⟨proof.b.x, proof.b.y.add Tornado.Protocol.BN254G2.Fp2.one⟩
    require (!badB.onCurve) "Malformed B test point unexpectedly on curve."
    expectError "Off-curve proof B was accepted."
      (verify key { proof with b := badB } signals)
    let tateJson ← readJson s!"{root}/bn254-tate-vectors.json"
    let nsRaw ← unwrap (← field tateJson "nonSubgroupG2").getArr?
    require (nsRaw.size == 4) "Expected four non-subgroup G2 limbs."
    let ns ← nsRaw.mapM decimal
    let nonSubgroupB : Tornado.Protocol.BN254G2.Affine := ⟨
      Tornado.Protocol.BN254G2.Fp2.ofNats ns[0]! ns[1]!,
      Tornado.Protocol.BN254G2.Fp2.ofNats ns[2]! ns[3]!⟩
    require nonSubgroupB.onCurve "Non-subgroup G2 point is off-curve."
    expectError "Non-subgroup proof B was accepted."
      (verify key { proof with b := nonSubgroupB } signals)
    expectError "Off-curve key IC was accepted."
      (verify { key with ic := key.ic.set! 0 badA } proof signals)
    expectError "Out-of-field proof A coordinate was accepted."
      (Tornado.Protocol.BN254G1.Affine.checked basePrime proof.a.y.val)
    expectError "Off-curve proof C coordinate was accepted."
      (Tornado.Protocol.BN254G1.Affine.checked proof.c.x.val (proof.c.y.val + 1))
    let finished ← IO.monoMsNow
    IO.println s!"PASS: pinned Classic proof accepted, all six changed signals and malformed inputs rejected, noble oracle matched ({finished - started} ms)"
    return (0 : UInt32)
  catch err =>
    IO.eprintln err.toString
    return (1 : UInt32)

end Tornado.Protocol.BN254Groth16Verify.Test

def main : IO UInt32 := Tornado.Protocol.BN254Groth16Verify.Test.main
