import TornadoProofs.Witness.PrimitiveSimulation

set_option autoImplicit false
namespace TornadoProofs.Witness.Execution
open Tornado.Protocol.WitnessVM
open Primitive

theorem primitive_shape_kind (primitive : Tornado.Protocol.WitnessVM.Primitive)
    (size : Nat) (shape : primitive.shapeValid size=true) :
    ∃ kind : Kind, primitive.kind=kind.tag ∧ primitive.inputs.size=kind.inputCount ∧
      primitive.outputs.size=kind.count := by
  have known (kind : Kind) (tag : primitive.kind=kind.tag) :
      ∃ kind : Kind, primitive.kind=kind.tag ∧ primitive.inputs.size=kind.inputCount ∧
        primitive.outputs.size=kind.count :=
    ⟨kind,tag,primitive_shape_dimensions primitive kind size tag shape⟩
  by_cases a : primitive.kind=Kind.montgomeryAdd.tag
  · exact known .montgomeryAdd a
  by_cases b : primitive.kind=Kind.montgomeryDouble.tag
  · exact known .montgomeryDouble b
  by_cases c : primitive.kind=Kind.edwards2Montgomery.tag
  · exact known .edwards2Montgomery c
  by_cases d : primitive.kind=Kind.montgomery2Edwards.tag
  · exact known .montgomery2Edwards d
  by_cases e : primitive.kind=Kind.babyAdd.tag
  · exact known .babyAdd e
  by_cases f : primitive.kind=Kind.window4.tag
  · exact known .window4 f
  by_cases g : primitive.kind=Kind.multiMux3.tag
  · exact known .multiMux3 g
  by_cases h : primitive.kind=Kind.square.tag
  · exact known .square h
  simp only [Kind.tag] at a b c d e f g h
  simp [Tornado.Protocol.WitnessVM.Primitive.shapeValid] at shape

end TornadoProofs.Witness.Execution
#print axioms TornadoProofs.Witness.Execution.primitive_shape_kind
