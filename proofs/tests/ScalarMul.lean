import LeanCrypto.BN254.G1

open LeanCrypto.BN254.G1

private def legacyScalarMul (point : Jacobian) (scalar : Nat) : Jacobian := Id.run do
  let mut factor := point
  let mut n := scalar % scalarPrime
  let mut result := Jacobian.infinity
  while n > 0 do
    if n % 2 == 1 then result := result.add factor
    factor := factor.double
    n := n / 2
  return result

private def sameRaw (a b : Jacobian) : Bool :=
  a.x.val == b.x.val && a.y.val == b.y.val && a.z.val == b.z.val

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def main : IO Unit := do
  let affine := Jacobian.ofAffine generator
  let doubled := affine.double
  let negative := Jacobian.ofAffine ⟨Fp.one, Fp.ofNat (basePrime - 2)⟩
  let rescaled : Jacobian := ⟨Fp.ofNat 49, Fp.ofNat 686, Fp.ofNat 7⟩
  let points := #[Jacobian.infinity, affine, doubled, negative, rescaled]
  let q := scalarPrime
  let scalars := #[0, 1, q-1, q, q+1, 2*q-1, 2*q, 2*q+1, 3*q+17, 2^512+q+1]
  for point in points do
    for scalar in scalars do
      let before := legacyScalarMul point scalar
      let after := point.scalarMul scalar
      require (sameRaw before after) s!"Raw scalar output changed for a public representative, scalar {scalar}."
    require (sameRaw (point.scalarMul q) Jacobian.infinity) "q reduction failed."
    require (sameRaw (point.scalarMul (q+1)) point) "q+1 reduction failed."
    require (sameRaw (point.scalarMul (2*q)) Jacobian.infinity) "2q reduction failed."
    require (sameRaw (point.scalarMul (2*q+1)) point) "2q+1 reduction failed."
  IO.println "PASS: 50 exact old/new raw G1 scalar comparisons on five public representatives, q/q+1/2q/2q+1 and 512-bit scalar boundaries, plus 20 modular-reduction expectations"
