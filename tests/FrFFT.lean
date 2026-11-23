import Lean
import Tornado.Protocol.FrFFT

open Lean Tornado.Protocol.FrFFT
open Tornado.Protocol.ProvingKey

private def unwrap (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{label}: {error}"

private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError label

private def natValue (value : Json) : Except String Nat := do
  let raw ← value.getStr?
  let some parsed := raw.toNat? | throw "Expected decimal Fr value."
  return parsed

private def natArray (value : Json) : Except String (Array Nat) := do
  let array ← value.getArr?
  array.mapM natValue

private def field (value : Json) (name : String) : Except String Json :=
  value.getObjVal? name

private def polynomials (value : Json) : Except String (Array Polynomial) := do
  let records ← value.getArr?
  records.mapM fun item => do
    let rows ← (← field item "entries").getArr?
    let entries ← rows.mapM fun row => do
      let constraint ← (← field row "constraint").getNat?
      let coefficient ← natValue (← field row "coefficient")
      return PolynomialEntry.mk constraint coefficient
    return Polynomial.mk entries

def main (args : List String) : IO Unit := do
  try
    let source := args[0]?.getD "fixtures/fr-fft-vectors.json"
    let fixture ← unwrap "read Fr FFT fixture" <|
      Json.parse (← IO.FS.readFile source)
    require ((← unwrap "fixture modulus" <| natValue (← unwrap "field" <| field fixture "modulus")) == modulus)
      "BN254 Fr modulus differs from the pinned fixture."
    require ((← unwrap "NQR" <| natValue (← unwrap "field" <| field fixture "nqr")) == nqr)
      "NQR differs from pinned SDK."
    require ((← unwrap "root32768" <| rootOfUnity 32768) ==
      (← unwrap "expected root32768" <| natValue (← unwrap "field" <| field fixture "omega32768")))
      "32768-point root differs from pinned noble FFT."
    require ((← unwrap "root65536" <| rootOfUnity 65536) ==
      (← unwrap "expected root65536" <| natValue (← unwrap "field" <| field fixture "omega65536")))
      "65536-point root differs from pinned noble FFT."
    require ((← unwrap "inverse32768" <| inverse 32768) ==
      (← unwrap "expected inverse32768" <| natValue (← unwrap "field" <| field fixture "inverse32768")))
      "32768 inverse differs from pinned noble Fr."
    let fftCases ← unwrap "FFT cases" <| (← unwrap "field" <| field fixture "fftCases").getArr?
    require (fftCases.size == 7) "Expected seven FFT cases."
    for testCase in fftCases do
      let n ← unwrap "FFT size" <| (← unwrap "field" <| field testCase "n").getNat?
      let input ← unwrap "FFT input" <| natArray (← unwrap "field" <| field testCase "input")
      let expected ← unwrap "FFT result" <| natArray (← unwrap "field" <| field testCase "transformed")
      require (input.size == n && expected.size == n) "FFT fixture size mismatch."
      require ((← unwrap "FFT" <| fft input) == expected)
        s!"Native forward FFT differs at n={n}."
      require ((← unwrap "inverse FFT" <| ifft expected) == input)
        s!"Native inverse FFT differs at n={n}."
    let large ← unwrap "large FFT fixture" <| field fixture "largeCase"
    let largeN ← unwrap "large FFT length" <| (← unwrap "field" <| field large "n").getNat?
    require (largeN == 32768) "Expected the pinned 32768-point domain."
    let mut largeInput := Array.replicate largeN 0
    let largeRows ← unwrap "large FFT nonzero terms" <|
      (← unwrap "field" <| field large "nonzero").getArr?
    for row in largeRows do
      let index ← unwrap "large FFT input index" <|
        (← unwrap "field" <| field row "index").getNat?
      let value ← unwrap "large FFT input value" <|
        natValue (← unwrap "field" <| field row "value")
      require (index < largeN) "Large FFT input index is out of bounds."
      largeInput := largeInput.set! index value
    let largeOutput ← unwrap "large FFT" <| fft largeInput
    let largeSamples ← unwrap "large FFT samples" <|
      (← unwrap "field" <| field large "samples").getArr?
    require (largeSamples.size == 8) "Expected eight large FFT samples."
    for sample in largeSamples do
      let index ← unwrap "large FFT sample index" <|
        (← unwrap "field" <| field sample "index").getNat?
      let expected ← unwrap "large FFT sample value" <|
        natValue (← unwrap "field" <| field sample "value")
      require (index < largeOutput.size && largeOutput[index]! == expected)
        s!"Native 32768-point FFT differs at index {index}."
    require ((← unwrap "large inverse FFT" <| ifft largeOutput) == largeInput)
      "Native 32768-point inverse FFT did not recover its input."
    let hCases ← unwrap "H cases" <| (← unwrap "field" <| field fixture "hCases").getArr?
    require (hCases.size == 3) "Expected three H cases."
    for testCase in hCases do
      let m ← unwrap "H domain" <| (← unwrap "field" <| field testCase "domainSize").getNat?
      let witness ← unwrap "H witness" <| natArray (← unwrap "field" <| field testCase "witness")
      let polsA ← unwrap "H A polynomials" <| polynomials (← unwrap "field" <| field testCase "polsA")
      let polsB ← unwrap "H B polynomials" <| polynomials (← unwrap "field" <| field testCase "polsB")
      let pA ← unwrap "H A evaluation" <| natArray (← unwrap "field" <| field testCase "pA")
      let pB ← unwrap "H B evaluation" <| natArray (← unwrap "field" <| field testCase "pB")
      let expected ← unwrap "H expected" <| natArray (← unwrap "field" <| field testCase "h")
      require ((← unwrap "sum A" <| sumEvaluations m witness polsA) == pA)
        s!"Sparse A accumulation differs at m={m}."
      require ((← unwrap "sum B" <| sumEvaluations m witness polsB) == pB)
        s!"Sparse B accumulation differs at m={m}."
      require ((← unwrap "calculate H" <| calculateH m witness polsA polsB) == expected)
        s!"High H polynomial differs at m={m}."
    require (!(fft #[]).isOk && !(fft #[1, 2, 3]).isOk &&
      !(fft #[modulus]).isOk && !(ifft #[modulus]).isOk)
      "Invalid FFT input was accepted."
    require (!(inverse 0).isOk && !(rootOfUnity 65537).isOk)
      "Invalid root or inverse was accepted."
    IO.println "PASS: 7 pinned NQR-7 FFT cases, 32768-point roundtrip, 3 sparse H polynomials, roots, and rejections"
    return ()
  catch error =>
    IO.eprintln error.toString
    throw error
