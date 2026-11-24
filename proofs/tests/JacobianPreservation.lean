import LeanCryptoProofs.CertifiedFields

open Lean LeanCrypto.BN254.G1

private def require (condition : Bool) (description : String) : IO Unit := do
  unless condition do throw <| IO.userError description

private def unwrap (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

private def samePoint (left right : Jacobian) : Bool :=
  left.x == right.x && left.y == right.y && left.z == right.z

private def projectiveEquation (point : Jacobian) : Bool :=
  point.y.pow 2 == (point.x.pow 3).add ((Fp.ofNat 3).mul (point.z.pow 6))

private def admissible (point : Jacobian) : Bool :=
  if point.isInfinity then samePoint point Jacobian.infinity else projectiveEquation point

private def rescale (point : Affine) (scale : Nat) : Jacobian :=
  let z := Fp.ofNat scale
  ⟨point.x.mul (z.pow 2), point.y.mul (z.pow 3), z⟩

private def decimal (json : Json) (field : String) : IO Nat := do
  let text ← unwrap <| json.getObjVal? field >>= Json.getStr?
  match text.toNat? with
  | none => throw <| IO.userError "Invalid public G1 fixture integer"
  | some value => pure value

def main : IO Unit := do
  let fixture ← unwrap <| Json.parse (← IO.FS.readFile "../packages/lean-crypto/fixtures/bn254-g1-vectors.json")
  let scalarRows ← unwrap <| fixture.getObjVal? "scalars" >>= Json.getArr?
  let mut originals : Array Affine := #[]
  for row in scalarRows do
    let result ← unwrap <| row.getObjVal? "result"
    if result != .null then
      let point ← unwrap <| Affine.checked (← decimal result "x") (← decimal result "y")
      originals := originals.push point
  require (originals.size >= 9) "Public G1 affine fixture coverage changed"
  let mut points := #[Jacobian.infinity]
  for point in originals do
    for scale in #[1, 2, 17, basePrime - 1] do
      let projective := rescale point scale
      require (!projective.isInfinity && admissible projective)
        "Independent scaled affine input violates the projective equation"
      points := points.push projective
  let mut additions := 0
  for left in points do
    require (admissible left.double) "Actual Jacobian.double left the admitted representation"
    require (samePoint (Jacobian.infinity.add left) left) "Left infinity identity changed coordinates"
    require (samePoint (left.add Jacobian.infinity) left) "Right infinity identity changed coordinates"
    for right in points do
      require (admissible (left.add right)) "Actual Jacobian.add left the admitted representation"
      additions := additions + 1
  for point in originals do
    let left := rescale point 2
    let same := rescale point 17
    let opposite : Jacobian := ⟨left.x, left.y.neg, left.z⟩
    require (admissible opposite) "Independent opposite point violates the curve equation"
    require (samePoint (left.add opposite) Jacobian.infinity)
      "Opposite-point branch did not produce canonical infinity"
    require (admissible (left.add same)) "Equal projective point with distinct scaling was rejected"
  require (!projectiveEquation Jacobian.infinity)
    "Negative control: native infinity sentinel unexpectedly satisfies the homogeneous equation"
  let malformedInfinity : Jacobian := ⟨Fp.one, Fp.ofNat 2, Fp.zero⟩
  require (!admissible malformedInfinity) "Negative control accepted noncanonical Z=0 input"
  require (samePoint malformedInfinity.double Jacobian.infinity)
    "Actual doubling no longer canonicalizes a Z=0 sentinel"
  let yZero : Jacobian := ⟨Fp.one, Fp.zero, Fp.one⟩
  require (!admissible yZero && samePoint yZero.double Jacobian.infinity)
    "Y=0 guard or off-curve negative control changed"
  let offCurve : Jacobian := ⟨Fp.one, Fp.ofNat 3, Fp.one⟩
  require (!admissible offCurve) "Negative control accepted an off-curve input"
  require (!(Affine.checked 1 3).isOk && !(Affine.checked basePrime 2).isOk)
    "Actual affine admission accepted an invalid input"
  require (additions >= 1300) "Projective addition matrix lost coverage"
  IO.println "PASS: actual G1 Jacobian add/double preserve public affine fixtures at four projective scalings, all addition branches, canonical infinity, and off-curve negative controls"
