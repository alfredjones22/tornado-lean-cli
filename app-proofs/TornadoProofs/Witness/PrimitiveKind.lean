import TornadoProofs.Witness.MultiMux

set_option autoImplicit false
namespace TornadoProofs.Witness.Primitive
open Field
open Tornado.Protocol.WitnessVM

inductive Kind where
  | montgomeryAdd | montgomeryDouble | edwards2Montgomery | montgomery2Edwards
  | babyAdd | window4 | multiMux3 | square
  deriving DecidableEq, BEq

def Kind.tag : Kind → String
  | .montgomeryAdd => "MontgomeryAdd"
  | .montgomeryDouble => "MontgomeryDouble"
  | .edwards2Montgomery => "Edwards2Montgomery"
  | .montgomery2Edwards => "Montgomery2Edwards"
  | .babyAdd => "BabyAdd"
  | .window4 => "Window4"
  | .multiMux3 => "MultiMux3"
  | .square => "Square"

def Kind.count : Kind → Nat
  | .montgomeryAdd => 3
  | .montgomeryDouble => 4
  | .edwards2Montgomery | .montgomery2Edwards => 2
  | .babyAdd => 6
  | .window4 | .square => 1
  | .multiMux3 => 19

def Kind.values : Kind → Array Nat → Array Nat
  | .montgomeryAdd => TornadoProofs.Witness.Primitive.montgomeryAdd
  | .montgomeryDouble => TornadoProofs.Witness.Primitive.montgomeryDouble
  | .edwards2Montgomery => TornadoProofs.Witness.Primitive.edwards2Montgomery
  | .montgomery2Edwards => TornadoProofs.Witness.Primitive.montgomery2Edwards
  | .babyAdd => TornadoProofs.Witness.Primitive.babyAdd
  | .window4 => TornadoProofs.Witness.Primitive.window4
  | .multiMux3 => TornadoProofs.Witness.Primitive.multiMux3
  | .square => TornadoProofs.Witness.Primitive.square

/-- Source-level field admissibility: independently nonzero denominators and
binary selectors. It does not mention native execution or R1CS acceptance. -/
def Kind.Admitted (kind : Kind) (i : Array Nat) : Prop :=
  match kind with
  | .montgomeryAdd => model (sub i[2]! i[0]!) ≠ 0
  | .montgomeryDouble => model (mul 2 i[1]!) ≠ 0
  | .edwards2Montgomery => model (sub 1 i[1]!) ≠ 0 ∧ model i[0]! ≠ 0
  | .montgomery2Edwards => model i[1]! ≠ 0 ∧ model (add i[0]! 1) ≠ 0
  | .babyAdd =>
    model (add 1 (mul 168696 (mul (mul i[0]! i[3]!) (mul i[1]! i[2]!)))) ≠ 0 ∧
    model (sub 1 (mul 168696 (mul (mul i[0]! i[3]!) (mul i[1]! i[2]!)))) ≠ 0
  | .window4 => i[1]! < 2
  | .multiMux3 => i[0]! < 2 ∧ i[1]! < 2 ∧ i[2]! < 2
  | .square => True

theorem Kind.construct (kind : Kind) (inputs : Array Nat)
    (admitted : kind.Admitted inputs) :
    primitiveValues kind.tag inputs = .ok (kind.values inputs) := by
  cases kind with
  | montgomeryAdd => exact montgomeryAdd_construct _ admitted
  | montgomeryDouble => exact montgomeryDouble_construct _ admitted
  | edwards2Montgomery => exact edwards2Montgomery_construct _ admitted.1 admitted.2
  | montgomery2Edwards => exact montgomery2Edwards_construct _ admitted.1 admitted.2
  | babyAdd => exact babyAdd_construct _ admitted.1 admitted.2
  | window4 => exact window4_construct _ admitted
  | multiMux3 => exact multiMux3_construct _ admitted.1 admitted.2.1 admitted.2.2
  | square => exact square_construct _

theorem Kind.shape (kind : Kind) (inputs : Array Nat) (bounded : Bounded inputs) :
    (kind.values inputs).size = kind.count ∧ Bounded (kind.values inputs) := by
  cases kind with
  | montgomeryAdd => exact montgomeryAdd_shape _
  | montgomeryDouble => exact montgomeryDouble_shape _
  | edwards2Montgomery => exact edwards2Montgomery_shape _
  | montgomery2Edwards => exact montgomery2Edwards_shape _
  | babyAdd => exact babyAdd_shape _
  | window4 => exact window4_shape _
  | multiMux3 => exact multiMux3_shape _ bounded
  | square => exact square_shape _

end TornadoProofs.Witness.Primitive
#print axioms TornadoProofs.Witness.Primitive.Kind.construct
#print axioms TornadoProofs.Witness.Primitive.Kind.shape
