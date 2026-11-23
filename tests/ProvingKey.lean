import Lean
import Tornado.Domain.NoteIdentity
import Tornado.Protocol.ProvingKey

open Lean Tornado.Domain Tornado.Protocol.ProvingKey
open Tornado.Protocol.Groth16Key

private def unwrap (label : String) (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{label}: {error}"

private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError label

private def stringField (json : Json) (name : String) : Except String String :=
  json.getObjVal? name >>= Json.getStr?

private def natField (json : Json) (name : String) : Except String Nat :=
  json.getObjVal? name >>= Json.getNat?

private def decimalField (json : Json) (name : String) : Except String Nat := do
  let raw ← stringField json name
  let some value := raw.toNat? | throw s!"Invalid decimal {name}."
  return value

private def expectedEntries (json : Json) : Except String (Array PolynomialEntry) := do
  let raw ← (← json.getObjVal? "entries").getArr?
  let mut entries := #[]
  for item in raw do
    entries := entries.push {
      constraint := (← natField item "constraint"),
      coefficient := (← decimalField item "coefficient") }
  return entries

private def mutatedByte (bytes : ByteArray) (index : Nat) (value : UInt8) : ByteArray :=
  ⟨bytes.data.set! index value⟩

def main (args : List String) : IO UInt32 := do
  let fixture ← unwrap "parse pinned proving-key vectors" <|
    Json.parse (← IO.FS.readFile "fixtures/proving-key-vectors.json")
  require ((← unwrap "source key hash" <| stringField fixture "sourceKeySha256") ==
    "8e2d2f22beafb5a9666daebca57b13f8029c3656c65fcfbcc86e2418fa16a3af")
    "Proving-key vector source hash differs from the pinned asset."
  require (fpRInverse == (← unwrap "Fp Montgomery inverse" <|
    decimalField fixture "fpRInv")) "Fp Montgomery inverse differs from the vector."
  require (frRInverse == (← unwrap "Fr Montgomery inverse" <|
    decimalField fixture "frRInv")) "Fr Montgomery inverse differs from the vector."
  require (!(authenticatePinnedKey ByteArray.empty).isOk)
    "A truncated proving key was authenticated."

  let pointSamples ← unwrap "point sample array" <|
    fixture.getObjVal? "pointSamples" >>= Json.getArr?
  require (pointSamples.size == 12) "Expected twelve key G1 point samples."
  for sample in pointSamples do
    let name ← unwrap "point name" <| stringField sample "name"
    let rawHex ← unwrap s!"{name} raw hex" <| stringField sample "rawHex"
    let raw ← unwrap s!"decode {name} raw bytes" <| parseHexBytes rawHex
    require (raw.size == 64) s!"{name} raw point is not 64 bytes."
    let decoded ← unwrap s!"decode {name} key point" <| readG1 raw 0
    require decoded.valid s!"{name} decoded point is invalid."
    let identity ← unwrap s!"{name} identity flag" <|
      sample.getObjVal? "identity" >>= Json.getBool?
    let x ← unwrap s!"{name} expected x" <| decimalField sample "x"
    let y ← unwrap s!"{name} expected y" <| decimalField sample "y"
    match decoded with
    | .identity => require identity s!"{name} expected a nonidentity point."
    | .point point =>
      require (!identity && point.x == x && point.y == y)
        s!"{name} canonical Fp coordinates differ from pinned SDK vectors."

  let firstRawHex ← unwrap "first point raw hex" <|
    stringField pointSamples[0]! "rawHex"
  let rawPoints ← unwrap "first point bytes" <| parseHexBytes firstRawHex
  require (readG1 rawPoints 0).isOk "First G1 point failed a repeat decode."
  require (!(readG1 rawPoints 1).isOk)
    "A truncated G1 point was accepted."
  let noncanonicalPoint : ByteArray := ⟨Array.replicate 64 255⟩
  require (!(readG1 noncanonicalPoint 0).isOk)
    "A noncanonical Montgomery Fp residue was accepted."
  let malformedY := mutatedByte rawPoints 32 (rawPoints[32]! + 1)
  require (!(readG1 malformedY 0).isOk)
    "A changed off-curve G1 point was accepted."

  let g2Samples ← unwrap "G2 sample array" <|
    fixture.getObjVal? "g2Samples" >>= Json.getArr?
  require (g2Samples.size == 5) "Expected five key G2 point samples."
  for item in g2Samples do
    let name ← unwrap "G2 point name" <| stringField item "name"
    let rawHex ← unwrap "G2 point raw hex" <| stringField item "rawHex"
    let raw ← unwrap s!"decode {name} raw bytes" <| parseHexBytes rawHex
    require (raw.size == 128) s!"{name} raw G2 point is not 128 bytes."
    let decoded ← unwrap s!"decode {name} G2 point" <| readG2 raw 0
    let identity ← unwrap "G2 identity flag" <|
      item.getObjVal? "identity" >>= Json.getBool?
    match decoded with
    | .identity => require identity s!"{name} expected a nonidentity G2 point."
    | .point point =>
      require (!identity && point.onCurve &&
        point.x.c0.val == (← unwrap "G2 x0" <| decimalField item "x0") &&
        point.x.c1.val == (← unwrap "G2 x1" <| decimalField item "x1") &&
        point.y.c0.val == (← unwrap "G2 y0" <| decimalField item "y0") &&
        point.y.c1.val == (← unwrap "G2 y1" <| decimalField item "y1"))
        s!"{name} canonical Fp2 coordinates differ from pinned SDK vectors."
  let firstG2Hex ← unwrap "first G2 raw hex" <| stringField g2Samples[0]! "rawHex"
  let firstG2 ← unwrap "first G2 raw bytes" <| parseHexBytes firstG2Hex
  require (!(readG2 firstG2 1).isOk) "A truncated G2 point was accepted."
  let noncanonicalG2 : ByteArray := ⟨Array.replicate 128 255⟩
  require (!(readG2 noncanonicalG2 0).isOk)
    "A noncanonical Montgomery G2 limb was accepted."

  let polynomialSamples ← unwrap "polynomial sample array" <|
    fixture.getObjVal? "polynomialSamples" >>= Json.getArr?
  require (polynomialSamples.size == 8) "Expected eight key polynomial samples."
  for sample in polynomialSamples do
    let category ← unwrap "polynomial section" <| stringField sample "section"
    let signal ← unwrap "polynomial signal" <| natField sample "signal"
    let rawHex ← unwrap "polynomial raw hex" <| stringField sample "rawHex"
    let raw ← unwrap s!"decode {category}[{signal}] raw bytes" <|
      parseHexBytes rawHex
    let (polynomial, next) ← unwrap s!"decode {category}[{signal}]" <|
      readPolynomialAt raw 0 raw.size 32768
    let expected ← unwrap "polynomial entries" <| expectedEntries sample
    require (next == raw.size && polynomial.entries == expected)
      s!"Native {category}[{signal}] differs from the pinned key."
    let sectionDecoded ← unwrap "decode one-record section" <|
      readPolynomialSection raw 0 raw.size 1 32768
    require (sectionDecoded.size == 1 && sectionDecoded[0]!.entries == expected)
      s!"One-record {category}[{signal}] section failed."
    require (!(readPolynomialAt raw 0 (raw.size - 1) 32768).isOk)
      "A truncated polynomial was accepted."

  let sampleHex ← unwrap "nonempty polynomial raw hex" <|
    stringField polynomialSamples[0]! "rawHex"
  let sample ← unwrap "nonempty polynomial bytes" <| parseHexBytes sampleHex
  require (sample.size >= 76) "Expected a two-entry polynomial sample."
  let duplicate := Id.run do
    let mut bytes := sample
    for i in [0:4] do bytes := mutatedByte bytes (40 + i) sample[4 + i]!
    return bytes
  require (!(readPolynomialAt duplicate 0 duplicate.size 32768).isOk)
    "A duplicate polynomial row was accepted."
  let mut invalidCoefficient := sample
  for i in [8:40] do invalidCoefficient := mutatedByte invalidCoefficient i 255
  require (!(readPolynomialAt invalidCoefficient 0 invalidCoefficient.size 32768).isOk)
    "A noncanonical Montgomery Fr coefficient was accepted."
  require (!(readPolynomialSection (sample.push 0) 0 (sample.size + 1) 1 32768).isOk)
    "Trailing polynomial section bytes were accepted."

  -- Passing the decompressed binary key path additionally checks every A/B
  -- polynomial record and the exact pinned section boundaries, entirely in Lean.
  if let [path] := args then
    let key ← IO.FS.readBinFile path
    let pinned ← unwrap "authenticate complete key bytes" <| authenticatePinnedKey key
    let parsed ← unwrap "decode every key section" <| decodeFullKey pinned
    require (parsed.polsA.size == 28300 && parsed.polsB.size == 28300 &&
      parsed.queryA.size == 28300 && parsed.queryB1.size == 28300 &&
      parsed.queryB2.size == 28300 && parsed.queryC.size == 28293 &&
      parsed.hExps.size == 32767)
      "Native key polynomial sections have the wrong number of signals."
    for item in polynomialSamples do
      let signal ← unwrap "sample signal" <| natField item "signal"
      let expected ← unwrap "sample polynomial entries" <| expectedEntries item
      let category ← unwrap "sample section" <| stringField item "section"
      let actual := if category == "A" then parsed.polsA[signal]!.entries
        else parsed.polsB[signal]!.entries
      require (actual == expected)
        s!"Full key {category}[{signal}] differs from its pinned sample."
    require (!(authenticatePinnedKey (mutatedByte key (key.size - 1)
      (key[key.size - 1]! + 1))).isOk)
      "A same-sized modified proving key was authenticated."
    IO.println "PASS: authenticated full key decoded all polynomial and query-point sections"

  IO.println "PASS: 12 native G1, 5 G2, and 8 sparse polynomial vectors match the pinned key"
  return 0
