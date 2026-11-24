import LeanCrypto.BN254.G2

/-! Circuit-independent Groth16 query and polynomial data. These public
structures do not authenticate a setup or certify witness validity. Query G2
points are checked on the twist by MSM; subgroup checks occur in verification. -/

namespace LeanCrypto.Groth16.Types

open LeanCrypto.BN254

structure AffineG1 where
  x : Nat
  y : Nat
  deriving Inhabited, Repr, BEq

inductive DecodedG1 where
  | identity
  | point (value : AffineG1)
  deriving Inhabited, Repr, BEq

def AffineG1.onCurve (point : AffineG1) : Bool :=
  point.x < LeanCrypto.BN254.Constants.basePrime && point.y < LeanCrypto.BN254.Constants.basePrime &&
  point.y * point.y % LeanCrypto.BN254.Constants.basePrime ==
    ((point.x * point.x % LeanCrypto.BN254.Constants.basePrime) * point.x + 3) % LeanCrypto.BN254.Constants.basePrime

def DecodedG1.valid : DecodedG1 → Bool
  | .identity => true
  | .point p => p.onCurve

inductive DecodedG2 where
  | identity
  | point (value : LeanCrypto.BN254.G2.Affine)

structure PolynomialEntry where
  constraint : Nat
  coefficient : Nat
  deriving Inhabited, Repr, BEq

structure Polynomial where
  entries : Array PolynomialEntry
  deriving Inhabited, Repr

structure QueryKey where
  nPublic : Nat
  vkAlpha1 : DecodedG1
  vkBeta1 : DecodedG1
  vkDelta1 : DecodedG1
  vkBeta2 : DecodedG2
  vkDelta2 : DecodedG2
  queryA : Array DecodedG1
  queryB1 : Array DecodedG1
  queryB2 : Array DecodedG2
  queryC : Array DecodedG1
  hExps : Array DecodedG1

structure ProofPoints where
  piA : G1.Jacobian
  piB : G2.Jacobian
  piC : G1.Jacobian
  publicSignals : Array Nat


instance : Inhabited DecodedG2 := ⟨.identity⟩
instance : Inhabited G1.Jacobian := ⟨.infinity⟩
instance : Inhabited G2.Jacobian := ⟨.infinity⟩

end LeanCrypto.Groth16.Types
