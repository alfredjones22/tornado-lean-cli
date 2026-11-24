import TornadoProofs.Witness.PrefixCanonical

open Lean Elab Term Meta in
elab "pedersenNativePoint" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `LeanCrypto.Pedersen `LeanCrypto.ExtendedPoint)
open Lean Elab Term Meta in
elab "pedersenNativeInverse" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `LeanCrypto.Pedersen `LeanCrypto.finv)
open Lean Elab Term Meta in
elab "pedersenNativeAffine" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `LeanCrypto.Pedersen `LeanCrypto.affine)
open Lean Elab Term Meta in
elab "pedersenNativeDecode" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `LeanCrypto.Pedersen `LeanCrypto.decodePoint)

open Lean Elab Term Meta in
elab "pedersenNativeX" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `LeanCrypto.Pedersen `LeanCrypto.ExtendedPoint.x)

open Lean Elab Term Meta in
elab "pedersenNativeY" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `LeanCrypto.Pedersen `LeanCrypto.ExtendedPoint.y)

open Lean Elab Term Meta in
elab "pedersenNativeZ" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `LeanCrypto.Pedersen `LeanCrypto.ExtendedPoint.z)

open Lean Elab Term Meta in
elab "pedersenNativeAccumulate" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `LeanCrypto.Pedersen `LeanCrypto.pedersenPoint)

set_option autoImplicit false
namespace TornadoProofs.Witness.Source
open Field

abbrev PedersenPoint := pedersenNativePoint
abbrev nativePedersenInverse (value : Nat) : Option Nat := pedersenNativeInverse value
abbrev nativePedersenAffine (point : PedersenPoint) : Option (Nat×Nat) := pedersenNativeAffine point
abbrev nativePedersenDecode (bytes : ByteArray) : Option PedersenPoint := pedersenNativeDecode bytes

abbrev nativePointX (point : PedersenPoint) : Nat := pedersenNativeX point

abbrev nativePointY (point : PedersenPoint) : Nat := pedersenNativeY point

abbrev nativePointZ (point : PedersenPoint) : Nat := pedersenNativeZ point

def affineReference (point : PedersenPoint) : Option (Nat×Nat) := do
  let inverse ← nativePedersenInverse (nativePointZ point)
  let x := mul (nativePointX point) inverse
  let y := mul (nativePointY point) inverse
  let x2 := mul x x
  let y2 := mul y y
  if add (mul 168700 x2) y2 != add 1 (mul 168696 (mul x2 y2)) then none
  else some (x,y)

theorem nativePedersenAffine_reference (point : PedersenPoint) :
    nativePedersenAffine point=affineReference point := rfl

theorem nativePedersenAffine_x_bound (point : PedersenPoint) (x y : Nat)
    (normalized : nativePedersenAffine point=some (x,y)) : x<q := by
  rw [nativePedersenAffine_reference] at normalized
  unfold affineReference at normalized
  cases inversion : nativePedersenInverse (nativePointZ point) with
  | none => simp [inversion,bind,Option.bind] at normalized
  | some inverse =>
    simp only [inversion,bind,Option.bind] at normalized
    split at normalized
    · cases normalized
    · have pair := Option.some.inj normalized
      have equal := congrArg Prod.fst pair
      change mul (nativePointX point) inverse=x at equal
      rw [← equal]
      exact mul_bounded _ _

/-- Canonical output range of the actual native primitive. Success here is a
source note-identity fact, never a VM/R1CS acceptance premise. -/
theorem pedersenX_bound (preimage : ByteArray) (value : Nat)
    (hashed : LeanCrypto.pedersenX preimage=.ok value) : value<q := by
  unfold LeanCrypto.pedersenX at hashed
  cases accumulated : pedersenNativeAccumulate preimage with
  | error err => simp [accumulated,bind,Except.bind] at hashed
  | ok point =>
    cases normalized : nativePedersenAffine point with
    | none => simp [accumulated,normalized,bind,Except.bind] at hashed
    | some pair =>
      obtain ⟨x,y⟩ := pair
      have equal : x=value := by
        simpa [accumulated,normalized,bind,Except.bind,pure,Except.pure] using hashed
      subst value
      exact nativePedersenAffine_x_bound point x y normalized

end TornadoProofs.Witness.Source
#print axioms TornadoProofs.Witness.Source.nativePedersenAffine_reference
#print axioms TornadoProofs.Witness.Source.nativePedersenAffine_x_bound
#print axioms TornadoProofs.Witness.Source.pedersenX_bound
