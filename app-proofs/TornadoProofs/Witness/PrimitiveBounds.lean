import TornadoProofs.Witness.PrimitiveValues

set_option autoImplicit false
namespace TornadoProofs.Witness.Primitive
open Field

def Bounded (values : Array Nat) : Prop := ∀ value ∈ values.toList, value < q

theorem montgomeryAdd_shape (inputs : Array Nat) :
    (montgomeryAdd inputs).size = 3 ∧ Bounded (montgomeryAdd inputs) := by
  simp [montgomeryAdd, Bounded, mul_bounded, sub_bounded]

theorem montgomeryDouble_shape (inputs : Array Nat) :
    (montgomeryDouble inputs).size = 4 ∧ Bounded (montgomeryDouble inputs) := by
  simp [montgomeryDouble, Bounded, mul_bounded, sub_bounded]

theorem edwards2Montgomery_shape (inputs : Array Nat) :
    (edwards2Montgomery inputs).size = 2 ∧ Bounded (edwards2Montgomery inputs) := by
  simp [edwards2Montgomery, Bounded, mul_bounded]

theorem montgomery2Edwards_shape (inputs : Array Nat) :
    (montgomery2Edwards inputs).size = 2 ∧ Bounded (montgomery2Edwards inputs) := by
  simp [montgomery2Edwards, Bounded, mul_bounded]

theorem babyAdd_shape (inputs : Array Nat) :
    (babyAdd inputs).size = 6 ∧ Bounded (babyAdd inputs) := by
  simp [babyAdd, Bounded, mul_bounded]

theorem window4_shape (inputs : Array Nat) :
    (window4 inputs).size = 1 ∧ Bounded (window4 inputs) := by
  simp [window4, Bounded, sub_bounded]

theorem square_shape (inputs : Array Nat) :
    (square inputs).size = 1 ∧ Bounded (square inputs) := by
  simp [square, Bounded, mul_bounded]

end TornadoProofs.Witness.Primitive
#print axioms TornadoProofs.Witness.Primitive.montgomeryAdd_shape
#print axioms TornadoProofs.Witness.Primitive.montgomeryDouble_shape
#print axioms TornadoProofs.Witness.Primitive.edwards2Montgomery_shape
#print axioms TornadoProofs.Witness.Primitive.montgomery2Edwards_shape
#print axioms TornadoProofs.Witness.Primitive.babyAdd_shape
#print axioms TornadoProofs.Witness.Primitive.window4_shape
#print axioms TornadoProofs.Witness.Primitive.square_shape
