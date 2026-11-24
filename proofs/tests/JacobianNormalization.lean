import LeanCryptoProofs.JacobianNormalization

open Lean LeanCrypto.BN254.G1

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def decimal (value : Json) (field : String) : IO Nat := do
  let text ← unwrap (value.getObjVal? field >>= Json.getStr?)
  match text.toNat? with
  | some value => pure value
  | none => throw (IO.userError "Invalid public G1 coordinate")

private def sameAffine (left right : Affine) : Bool := left.x == right.x && left.y == right.y

private def rescale (point : Affine) (scale : Nat) : Jacobian :=
  let z := Fp.ofNat scale
  ⟨point.x.mul (z.pow 2), point.y.mul (z.pow 3), z⟩

private def normalizeNative (point : Jacobian) : IO (Option Affine) := unwrap point.toAffine

def main : IO Unit := do
  let fixture ← unwrap (Json.parse (← IO.FS.readFile "../packages/lean-crypto/fixtures/bn254-g1-vectors.json"))
  let rows ← unwrap (fixture.getObjVal? "scalars" >>= Json.getArr?)
  let mut cases := 0
  for row in rows do
    let coordinates ← unwrap (row.getObjVal? "result")
    if coordinates != .null then
      let original ← unwrap (Affine.checked (← decimal coordinates "x") (← decimal coordinates "y"))
      for scale in #[1, 2, 17, basePrime - 1] do
        let projective := rescale original scale
        require (!projective.isInfinity) "Finite public point became infinity"
        let some result ← normalizeNative projective | throw (IO.userError "Actual normalizeNativer rejected a finite public point")
        require (sameAffine result original && result.onCurve)
          "Actual normalization disagrees with independently rescaled affine input"
        let some repeated ← normalizeNative (Jacobian.ofAffine result) |
          throw (IO.userError "Actual affine roundtrip produced infinity")
        require (sameAffine repeated result) "Affine normalization is not idempotent"
        let doubled := projective.double
        let doubledResult ← normalizeNative doubled
        match doubledResult with
        | none => require doubled.isInfinity "Finite doubled point lost its affine result"
        | some point => require point.onCurve "Normalized double is off-curve"
        cases := cases + 1
  require (cases >= 36) "Public normalization fixture coverage changed"
  require ((← normalizeNative Jacobian.infinity).isNone) "Canonical infinity did not normalizeNative to none"
  let malformedInfinity : Jacobian := ⟨Fp.one, Fp.ofNat 2, Fp.zero⟩
  require ((← normalizeNative malformedInfinity).isNone)
    "Actual normalizeNativer's Z=0 branch changed outside the admitted theorem scope"
  let offCurve : Jacobian := ⟨Fp.one, Fp.ofNat 3, Fp.one⟩
  require (!(offCurve.toAffine).isOk) "Off-curve negative control bypassed normalization guard"
  let tinyOffCurve : Jacobian := ⟨Fp.zero, Fp.zero, Fp.one⟩
  require (!(tinyOffCurve.toAffine).isOk) "Zero-coordinate off-curve negative control bypassed guard"
  IO.println "PASS: actual G1 normalization of public affine fixtures at four projective scalings, affine roundtrip, doubles, infinity and off-curve guards"
