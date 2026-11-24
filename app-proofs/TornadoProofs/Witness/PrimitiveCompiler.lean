import TornadoProofs.Witness.MultiMuxRecipes
import TornadoProofs.Witness.OrderedArrays

set_option autoImplicit false
namespace TornadoProofs.Witness.Primitive
open Field Symbolic Execution
open Tornado.Protocol.WitnessSymbolic

def Kind.inputCount : Kind → Nat
  | .montgomeryAdd | .babyAdd => 4
  | .montgomeryDouble | .edwards2Montgomery | .montgomery2Edwards | .window4 => 2
  | .multiMux3 => 19
  | .square => 1

theorem Kind.recipe (kind : Kind) (inputIDs values : Array Nat)
    (size : inputIDs.size=kind.inputCount)
    (admitted : kind.Admitted (inputIDs.map (values[·]!))) :
    (primitiveExpressions kind.tag inputIDs).map (expressionValue values) =
      kind.values (inputIDs.map (values[·]!)) := by
  cases kind with
  | montgomeryAdd => exact montgomeryAdd_recipe _ _ size admitted
  | montgomeryDouble => exact montgomeryDouble_recipe _ _ size admitted
  | edwards2Montgomery => exact edwards2Montgomery_recipe _ _ size admitted
  | montgomery2Edwards => exact montgomery2Edwards_recipe _ _ size admitted
  | babyAdd => exact babyAdd_recipe _ _ size admitted
  | window4 => exact window4_recipe _ _ size
  | multiMux3 => exact multiMux3_recipe _ _ size
  | square => exact square_recipe _ _ size

/-- Actual public DAG compilation yields the independent arithmetic values
consumed by the native primitive constructor, in original output order. -/
theorem compilePrimitive_values (resolver : Resolver) (inputs values : Array Nat)
    (denotes : Denotes resolver.nodes inputs values) (kind : Kind)
    (inputIDs outputIDs : Array Nat)
    (size : inputIDs.size=kind.inputCount)
    (admitted : kind.Admitted (inputIDs.map (values[·]!)))
    (compiled : compilePrimitive resolver kind.tag inputIDs = .ok outputIDs) :
    outputIDs.map (values[·]!) = kind.values (inputIDs.map (values[·]!)) := by
  have mapped := arrayMapM_value (Expression.compile resolver)
    (primitiveExpressions kind.tag inputIDs) outputIDs
    (expressionValue values) (values[·]!)
    (fun expression node returned => compileExpression_sound resolver inputs values denotes expression node returned)
    compiled
  exact mapped.trans (kind.recipe inputIDs values size admitted)

end TornadoProofs.Witness.Primitive
#print axioms TornadoProofs.Witness.Primitive.Kind.recipe
#print axioms TornadoProofs.Witness.Primitive.compilePrimitive_values
