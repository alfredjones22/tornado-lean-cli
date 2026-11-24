import TornadoProofs.Witness.PrimitiveEquations
import TornadoProofs.Witness.PrimitiveBounds

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace TornadoProofs.Witness.Primitive
open Field

def coordinateValues (inputs : Array Nat) (coordinate s0 s1 s2 s10 : Nat) : Array Nat :=
  let start := 3 + coordinate * 8
  let c0 := inputs[start]!
  let c1 := inputs[start+1]!
  let c2 := inputs[start+2]!
  let c3 := inputs[start+3]!
  let c4 := inputs[start+4]!
  let c5 := inputs[start+5]!
  let c6 := inputs[start+6]!
  let c7 := inputs[start+7]!
  let a210 := mul (sub (add (add (sub (add (sub (sub c7 c6) c5) c4) c3) c2) c1) c0) s10
  let a21 := mul (add (sub (sub c6 c4) c2) c0) s1
  let a20 := mul (add (sub (sub c5 c4) c1) c0) s0
  let a2 := sub c4 c0
  let a10 := mul (add (sub (sub c3 c2) c1) c0) s10
  let a1 := mul (sub c2 c0) s1
  let a0 := mul (sub c1 c0) s0
  let out := add (mul (add (add (add a210 a21) a20) a2) s2)
    (add (add (add a10 a1) a0) c0)
  #[a210,a21,a20,a2,a10,a1,a0,c0,out]

theorem muxCoordinate_eq (inputs : Array Nat) (coordinate s0 s1 s2 s10 : Nat) :
    muxCoordinate inputs coordinate s0 s1 s2 s10 =
      coordinateValues inputs coordinate s0 s1 s2 s10 := rfl

def CoordinateEquations (inputs : Array Nat) (coordinate : Nat)
    (s0 s1 s2 s10 : Nat) (o : Array Nat) : Prop :=
  let c := fun i => model inputs[3+coordinate*8+i]!
  model o[0]! = (c 7-c 6-c 5+c 4-c 3+c 2+c 1-c 0)*model s10 ∧
  model o[1]! = (c 6-c 4-c 2+c 0)*model s1 ∧
  model o[2]! = (c 5-c 4-c 1+c 0)*model s0 ∧
  model o[3]! = c 4-c 0 ∧
  model o[4]! = (c 3-c 2-c 1+c 0)*model s10 ∧
  model o[5]! = (c 2-c 0)*model s1 ∧
  model o[6]! = (c 1-c 0)*model s0 ∧
  model o[7]! = c 0 ∧
  (model o[0]!+model o[1]!+model o[2]!+model o[3]!)*model s2 =
    model o[8]!-(model o[4]!+model o[5]!+model o[6]!+c 0)

theorem coordinate_equations (inputs : Array Nat) (coordinate s0 s1 s2 s10 : Nat) :
    CoordinateEquations inputs coordinate s0 s1 s2 s10
      (coordinateValues inputs coordinate s0 s1 s2 s10) := by
  simp only [CoordinateEquations, coordinateValues]
  simp only [getElem!_def, List.getElem?_toArray, List.getElem?_cons_zero,
    List.getElem?_cons_succ] at *
  simp only [model_sub, model_mul, model_add]
  repeat' constructor
  all_goals ring_nf

theorem bounded_get (inputs : Array Nat) (bounded : Bounded inputs) (index : Nat) :
    inputs[index]! < q := by
  by_cases bound : index < inputs.size
  · rw [getElem!_pos inputs index bound]
    exact bounded _ (by simp)
  · rw [getElem!_neg inputs index bound]
    decide

theorem coordinate_shape (inputs : Array Nat) (coordinate s0 s1 s2 s10 : Nat)
    (bounded : Bounded inputs) :
    (coordinateValues inputs coordinate s0 s1 s2 s10).size = 9 ∧
      Bounded (coordinateValues inputs coordinate s0 s1 s2 s10) := by
  simp [coordinateValues, Bounded, mul_bounded, sub_bounded, add_bounded,
    bounded_get inputs bounded]

theorem multiMux3_shape (inputs : Array Nat) (bounded : Bounded inputs) :
    (multiMux3 inputs).size = 19 ∧ Bounded (multiMux3 inputs) := by
  have first := (coordinate_shape inputs 0 inputs[0]! inputs[1]! inputs[2]!
    (mul inputs[1]! inputs[0]!) bounded).2
  have second := (coordinate_shape inputs 1 inputs[0]! inputs[1]! inputs[2]!
    (mul inputs[1]! inputs[0]!) bounded).2
  simp [multiMux3, muxCoordinate_eq, Bounded, mul_bounded,
    bounded_get _ first, bounded_get _ second]

def coordinateAt (output : Array Nat) (coordinate : Nat) : Array Nat :=
  #[output[1+coordinate]!,output[3+coordinate]!,output[5+coordinate]!,
    output[7+coordinate]!,output[9+coordinate]!,output[11+coordinate]!,
    output[13+coordinate]!,output[15+coordinate]!,output[17+coordinate]!]

def interleave (s10 : Nat) (a b : Array Nat) : Array Nat :=
  #[s10,a[0]!,b[0]!,a[1]!,b[1]!,a[2]!,b[2]!,a[3]!,b[3]!,
    a[4]!,b[4]!,a[5]!,b[5]!,a[6]!,b[6]!,a[7]!,b[7]!,a[8]!,b[8]!]

theorem coordinateAt_interleave (s10 : Nat) (a b : Array Nat)
    (ha : a.size = 9) (hb : b.size = 9) :
    coordinateAt (interleave s10 a b) 0 = a ∧
    coordinateAt (interleave s10 a b) 1 = b := by
  constructor
  all_goals apply Array.ext
  · simpa only [coordinateAt, List.size_toArray, List.length_cons,
      List.length_nil, Nat.reduceAdd] using ha.symm
  · intro index leftBound rightBound
    have bound : index < 9 := by simpa only [coordinateAt, List.size_toArray,
      List.length_cons, List.length_nil, Nat.reduceAdd] using leftBound
    interval_cases index <;> simp [coordinateAt, interleave, ha]
  · simpa only [coordinateAt, List.size_toArray, List.length_cons,
      List.length_nil, Nat.reduceAdd] using hb.symm
  · intro index leftBound rightBound
    have bound : index < 9 := by simpa only [coordinateAt, List.size_toArray,
      List.length_cons, List.length_nil, Nat.reduceAdd] using leftBound
    interval_cases index <;> simp [coordinateAt, interleave, hb]

theorem multiMux3_interleave (inputs : Array Nat) :
    multiMux3 inputs = interleave (mul inputs[1]! inputs[0]!)
      (coordinateValues inputs 0 inputs[0]! inputs[1]! inputs[2]! (mul inputs[1]! inputs[0]!))
      (coordinateValues inputs 1 inputs[0]! inputs[1]! inputs[2]! (mul inputs[1]! inputs[0]!)) := by
  simp only [multiMux3, muxCoordinate_eq, interleave]

theorem coordinateAt_first (inputs : Array Nat) :
    coordinateAt (multiMux3 inputs) 0 =
      coordinateValues inputs 0 inputs[0]! inputs[1]! inputs[2]!
        (mul inputs[1]! inputs[0]!) := by
  rw [multiMux3_interleave]
  exact (coordinateAt_interleave _ _ _ rfl rfl).1

theorem coordinateAt_second (inputs : Array Nat) :
    coordinateAt (multiMux3 inputs) 1 =
      coordinateValues inputs 1 inputs[0]! inputs[1]! inputs[2]!
        (mul inputs[1]! inputs[0]!) := by
  rw [multiMux3_interleave]
  exact (coordinateAt_interleave _ _ _ rfl rfl).2

theorem multiMux3_equations (inputs : Array Nat) :
    model (multiMux3 inputs)[0]! = model inputs[1]! * model inputs[0]! ∧
    CoordinateEquations inputs 0 inputs[0]! inputs[1]! inputs[2]!
      (mul inputs[1]! inputs[0]!) (coordinateAt (multiMux3 inputs) 0) ∧
    CoordinateEquations inputs 1 inputs[0]! inputs[1]! inputs[2]!
      (mul inputs[1]! inputs[0]!) (coordinateAt (multiMux3 inputs) 1) := by
  constructor
  · change model (mul inputs[1]! inputs[0]!) = _
    exact model_mul _ _
  rw [coordinateAt_first, coordinateAt_second]
  exact ⟨coordinate_equations _ _ _ _ _ _, coordinate_equations _ _ _ _ _ _⟩

end TornadoProofs.Witness.Primitive
#print axioms TornadoProofs.Witness.Primitive.muxCoordinate_eq
#print axioms TornadoProofs.Witness.Primitive.coordinate_equations
#print axioms TornadoProofs.Witness.Primitive.bounded_get
#print axioms TornadoProofs.Witness.Primitive.coordinate_shape
#print axioms TornadoProofs.Witness.Primitive.multiMux3_shape
#print axioms TornadoProofs.Witness.Primitive.coordinateAt_first
#print axioms TornadoProofs.Witness.Primitive.coordinateAt_second
#print axioms TornadoProofs.Witness.Primitive.multiMux3_equations

#print axioms TornadoProofs.Witness.Primitive.coordinateAt_interleave
#print axioms TornadoProofs.Witness.Primitive.multiMux3_interleave
