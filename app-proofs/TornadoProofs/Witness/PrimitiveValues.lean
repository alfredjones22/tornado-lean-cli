import TornadoProofs.Witness.NativeField
import Init.Data.Range.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Constructive arithmetic for every instantiated native primitive. All
inverses below are mathematical field inverses; successful VM or R1CS execution
is never an input premise. Circuit wiring/assignment is handled separately. -/
set_option autoImplicit false
namespace TornadoProofs.Witness.Primitive

open Tornado.Protocol.WitnessVM
open Field

def invValue (x : Nat) : Nat := ((model x)⁻¹).val

def montgomeryAdd (inputs : Array Nat) : Array Nat :=
  let x1 := inputs[0]!
  let y1 := inputs[1]!
  let x2 := inputs[2]!
  let y2 := inputs[3]!
  let slope := mul (sub y2 y1) (invValue (sub x2 x1))
  let x := sub (sub (sub (mul slope slope) 168698) x1) x2
  #[slope, x, sub (mul slope (sub x1 x)) y1]

def montgomeryDouble (inputs : Array Nat) : Array Nat :=
  let x := inputs[0]!
  let y := inputs[1]!
  let squared := mul x x
  let numerator := add (add (mul 3 squared) (mul (2 * 168698) x)) 1
  let slope := mul numerator (invValue (mul 2 y))
  let outX := sub (sub (mul slope slope) 168698) (mul 2 x)
  #[squared, slope, outX, sub (mul slope (sub x outX)) y]

def edwards2Montgomery (inputs : Array Nat) : Array Nat :=
  let x := inputs[0]!
  let y := inputs[1]!
  let outX := mul (add 1 y) (invValue (sub 1 y))
  #[outX, mul outX (invValue x)]

def montgomery2Edwards (inputs : Array Nat) : Array Nat :=
  let x := inputs[0]!
  let y := inputs[1]!
  #[mul x (invValue y), mul (sub x 1) (invValue (add x 1))]

def babyAdd (inputs : Array Nat) : Array Nat :=
  let x1 := inputs[0]!
  let y1 := inputs[1]!
  let x2 := inputs[2]!
  let y2 := inputs[3]!
  let beta := mul x1 y2
  let gamma := mul y1 x2
  let delta := mul (sub y1 (mul 168700 x1)) (add x2 y2)
  let tau := mul beta gamma
  let x := mul (add beta gamma) (invValue (add 1 (mul 168696 tau)))
  let y := mul (sub (add delta (mul 168700 beta)) gamma) (invValue (sub 1 (mul 168696 tau)))
  #[beta, gamma, delta, tau, x, y]

def window4 (inputs : Array Nat) : Array Nat :=
  #[sub inputs[0]! (mul (mul 2 inputs[0]!) inputs[1]!)]

def square (inputs : Array Nat) : Array Nat := #[mul inputs[0]! inputs[0]!]

-- This named reference is identical to the private helper and makes its
-- nineteen-output interleaving explicit without a shadow final checker.
open Lean Elab Term Meta in
elab "vmMuxCoordinate" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `Tornado.Protocol.WitnessVM `Tornado.Protocol.WitnessVM.muxCoordinate)

def muxCoordinate (inputs : Array Nat) (coordinate s0 s1 s2 s10 : Nat) : Array Nat :=
  vmMuxCoordinate inputs coordinate s0 s1 s2 s10

def multiMux3 (inputs : Array Nat) : Array Nat :=
  let s0 := inputs[0]!
  let s1 := inputs[1]!
  let s2 := inputs[2]!
  let s10 := mul s1 s0
  let first := muxCoordinate inputs 0 s0 s1 s2 s10
  let second := muxCoordinate inputs 1 s0 s1 s2 s10
  #[s10, first[0]!, second[0]!, first[1]!, second[1]!,
    first[2]!, second[2]!, first[3]!, second[3]!,
    first[4]!, second[4]!, first[5]!, second[5]!,
    first[6]!, second[6]!, first[7]!, second[7]!, first[8]!, second[8]!]

theorem montgomeryAdd_construct (inputs : Array Nat)
    (denominator : model (sub inputs[2]! inputs[0]!) ≠ 0) :
    primitiveValues "MontgomeryAdd" inputs = .ok (montgomeryAdd inputs) := by
  simp only [primitiveValues]
  change (do let i ← inverse (sub inputs[2]! inputs[0]!)
             pure #[mul (sub inputs[3]! inputs[1]!) i,
               sub (sub (sub (mul (mul (sub inputs[3]! inputs[1]!) i)
                 (mul (sub inputs[3]! inputs[1]!) i)) 168698) inputs[0]!) inputs[2]!,
               sub (mul (mul (sub inputs[3]! inputs[1]!) i)
                 (sub inputs[0]! (sub (sub (sub (mul (mul (sub inputs[3]! inputs[1]!) i)
                   (mul (sub inputs[3]! inputs[1]!) i)) 168698) inputs[0]!) inputs[2]!))) inputs[1]!]) = _
  rw [inverse_construct _ denominator]
  rfl

theorem montgomeryDouble_construct (inputs : Array Nat)
    (denominator : model (mul 2 inputs[1]!) ≠ 0) :
    primitiveValues "MontgomeryDouble" inputs = .ok (montgomeryDouble inputs) := by
  simp only [primitiveValues]
  change (do let i ← inverse (mul 2 inputs[1]!)
             let squared := mul inputs[0]! inputs[0]!
             let numerator := add (add (mul 3 squared) (mul (2 * 168698) inputs[0]!)) 1
             let slope := mul numerator i
             let x := sub (sub (mul slope slope) 168698) (mul 2 inputs[0]!)
             pure #[squared, slope, x, sub (mul slope (sub inputs[0]! x)) inputs[1]!]) = _
  rw [inverse_construct _ denominator]
  rfl

theorem edwards2Montgomery_construct (inputs : Array Nat)
    (oneMinusY : model (sub 1 inputs[1]!) ≠ 0) (x : model inputs[0]! ≠ 0) :
    primitiveValues "Edwards2Montgomery" inputs = .ok (edwards2Montgomery inputs) := by
  simp only [primitiveValues]
  change (do let i ← inverse (sub 1 inputs[1]!)
             let j ← inverse inputs[0]!
             let outX := mul (add 1 inputs[1]!) i
             pure #[outX, mul outX j]) = _
  rw [inverse_construct _ oneMinusY, inverse_construct _ x]
  rfl

theorem montgomery2Edwards_construct (inputs : Array Nat)
    (y : model inputs[1]! ≠ 0) (onePlusX : model (add inputs[0]! 1) ≠ 0) :
    primitiveValues "Montgomery2Edwards" inputs = .ok (montgomery2Edwards inputs) := by
  simp only [primitiveValues]
  change (do let i ← inverse inputs[1]!
             let j ← inverse (add inputs[0]! 1)
             pure #[mul inputs[0]! i, mul (sub inputs[0]! 1) j]) = _
  rw [inverse_construct _ y, inverse_construct _ onePlusX]
  rfl

theorem babyAdd_construct (inputs : Array Nat)
    (plus : model (add 1 (mul 168696 (mul (mul inputs[0]! inputs[3]!)
      (mul inputs[1]! inputs[2]!)))) ≠ 0)
    (minus : model (sub 1 (mul 168696 (mul (mul inputs[0]! inputs[3]!)
      (mul inputs[1]! inputs[2]!)))) ≠ 0) :
    primitiveValues "BabyAdd" inputs = .ok (babyAdd inputs) := by
  simp only [primitiveValues]
  change (do
    let beta := mul inputs[0]! inputs[3]!
    let gamma := mul inputs[1]! inputs[2]!
    let delta := mul (sub inputs[1]! (mul 168700 inputs[0]!)) (add inputs[2]! inputs[3]!)
    let tau := mul beta gamma
    let i ← inverse (add 1 (mul 168696 tau))
    let j ← inverse (sub 1 (mul 168696 tau))
    pure #[beta, gamma, delta, tau, mul (add beta gamma) i,
      mul (sub (add delta (mul 168700 beta)) gamma) j]) = _
  dsimp only
  rw [inverse_construct _ plus, inverse_construct _ minus]
  rfl

theorem window4_construct (inputs : Array Nat) (bit : inputs[1]! < 2) :
    primitiveValues "Window4" inputs = .ok (window4 inputs) := by
  simp only [primitiveValues]
  have legal : ¬inputs[1]! > 1 := by omega
  simp only [legal, ↓reduceIte, window4]
  rfl

theorem square_construct (inputs : Array Nat) :
    primitiveValues "Square" inputs = .ok (square inputs) := by
  rfl

set_option maxHeartbeats 2000000 in
theorem multiMux3_construct (inputs : Array Nat)
    (s0 : inputs[0]! < 2) (s1 : inputs[1]! < 2) (s2 : inputs[2]! < 2) :
    primitiveValues "MultiMux3" inputs = .ok (multiMux3 inputs) := by
  simp only [primitiveValues]
  have legal : ¬((inputs[0]! > 1 ∨ inputs[1]! > 1) ∨ inputs[2]! > 1) := by omega
  simp only [Bool.or_eq_true, decide_eq_true_eq, legal, ↓reduceIte]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rfl

end TornadoProofs.Witness.Primitive

#print axioms TornadoProofs.Witness.Primitive.montgomeryAdd_construct
#print axioms TornadoProofs.Witness.Primitive.montgomeryDouble_construct
#print axioms TornadoProofs.Witness.Primitive.edwards2Montgomery_construct
#print axioms TornadoProofs.Witness.Primitive.montgomery2Edwards_construct
#print axioms TornadoProofs.Witness.Primitive.babyAdd_construct
#print axioms TornadoProofs.Witness.Primitive.window4_construct
#print axioms TornadoProofs.Witness.Primitive.square_construct
#print axioms TornadoProofs.Witness.Primitive.multiMux3_construct
