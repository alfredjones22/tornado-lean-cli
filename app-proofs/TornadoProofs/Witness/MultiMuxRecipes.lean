import TornadoProofs.Witness.PrimitiveRecipes

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Primitive
open Field
open Symbolic
open Tornado.Protocol.WitnessSymbolic

open Lean Elab Term Meta in
elab "symbolicCoordinate" : term => mkConstWithFreshMVarLevels (mkPrivateNameCore
  `Tornado.Protocol.WitnessExpressions `Tornado.Protocol.WitnessSymbolic.expressionCoordinate)

def coordinateExpressions (inputs : Array Expression) (coordinate : Nat)
    (s0 s1 s2 s10 : Expression) : Array Expression :=
  let start := 3+coordinate*8
  let c0 := inputs[start]!
  let c1 := inputs[start+1]!
  let c2 := inputs[start+2]!
  let c3 := inputs[start+3]!
  let c4 := inputs[start+4]!
  let c5 := inputs[start+5]!
  let c6 := inputs[start+6]!
  let c7 := inputs[start+7]!
  let a210 := .mul (.sub (.add (.add (.sub (.add (.sub (.sub c7 c6) c5) c4) c3) c2) c1) c0) s10
  let a21 := .mul (.add (.sub (.sub c6 c4) c2) c0) s1
  let a20 := .mul (.add (.sub (.sub c5 c4) c1) c0) s0
  let a2 := .sub c4 c0
  let a10 := .mul (.add (.sub (.sub c3 c2) c1) c0) s10
  let a1 := .mul (.sub c2 c0) s1
  let a0 := .mul (.sub c1 c0) s0
  let out := .add (.mul (.add (.add (.add a210 a21) a20) a2) s2)
    (.add (.add (.add a10 a1) a0) c0)
  #[a210,a21,a20,a2,a10,a1,a0,c0,out]


theorem coordinateExpressions_actual (inputs : Array Expression) (coordinate : Nat)
    (s0 s1 s2 s10 : Expression) :
    symbolicCoordinate inputs coordinate s0 s1 s2 s10 =
      coordinateExpressions inputs coordinate s0 s1 s2 s10 := rfl

theorem coordinateExpressions_size (inputs : Array Expression) (coordinate : Nat)
    (s0 s1 s2 s10 : Expression) :
    (coordinateExpressions inputs coordinate s0 s1 s2 s10).size = 9 := rfl

theorem expression_get_value (expressions : Array Expression) (values : Array Nat)
    (index : Nat) (bound : index < expressions.size) :
    expressionValue values expressions[index]! =
      (expressions.map (expressionValue values))[index]! := by
  simp [getElem!_pos, bound]

theorem coordinate_recipe (inputIDs values : Array Nat) (size : inputIDs.size=19)
    (coordinate : Nat) (binary : coordinate=0 ∨ coordinate=1)
    (s0 s1 s2 s10 : Expression) :
    (coordinateExpressions (inputIDs.map Expression.reference) coordinate s0 s1 s2 s10).map
        (expressionValue values) =
      coordinateValues (inputIDs.map (values[·]!)) coordinate
        (expressionValue values s0) (expressionValue values s1)
        (expressionValue values s2) (expressionValue values s10) := by
  rcases binary with rfl | rfl
  all_goals
    simp [coordinateExpressions, coordinateValues, expressionValue,
      getElem!_pos, size, mul_eq, sub_eq, add_eq, LeanCrypto.Groth16.FFT.mul,
      LeanCrypto.Groth16.FFT.sub, LeanCrypto.Groth16.FFT.add,
      show LeanCrypto.Groth16.FFT.modulus=q from rfl]

def interleaveExpressions (s : Expression) (a b : Array Expression) : Array Expression :=
  #[s,a[0]!,b[0]!,a[1]!,b[1]!,a[2]!,b[2]!,a[3]!,b[3]!,a[4]!,b[4]!,
    a[5]!,b[5]!,a[6]!,b[6]!,a[7]!,b[7]!,a[8]!,b[8]!]

theorem interleaveExpressions_value (values : Array Nat) (s : Expression) (a b : Array Expression)
    (aSize : a.size=9) (bSize : b.size=9) :
    (interleaveExpressions s a b).map (expressionValue values) =
      interleave (expressionValue values s) (a.map (expressionValue values))
        (b.map (expressionValue values)) := by
  simp [interleaveExpressions,interleave,getElem!_pos,aSize,bSize]

theorem primitiveExpressions_multiMux3 (inputIDs : Array Nat) :
    primitiveExpressions "MultiMux3" inputIDs =
      let inputs := inputIDs.map Expression.reference
      let s10 := Expression.mul inputs[1]! inputs[0]!
      interleaveExpressions s10
        (coordinateExpressions inputs 0 inputs[0]! inputs[1]! inputs[2]! s10)
        (coordinateExpressions inputs 1 inputs[0]! inputs[1]! inputs[2]! s10) := by
  simp only [primitiveExpressions, coordinateExpressions_actual, interleaveExpressions]
  rfl

theorem multiMux3_recipe (inputIDs values : Array Nat) (size : inputIDs.size=19) :
    (primitiveExpressions "MultiMux3" inputIDs).map (expressionValue values) =
      multiMux3 (inputIDs.map (values[·]!)) := by
  rw [primitiveExpressions_multiMux3]
  dsimp only
  rw [interleaveExpressions_value values _ _ _ (coordinateExpressions_size _ _ _ _ _ _)
    (coordinateExpressions_size _ _ _ _ _ _)]
  rw [coordinate_recipe inputIDs values size 0 (Or.inl rfl),
    coordinate_recipe inputIDs values size 1 (Or.inr rfl)]
  rw [multiMux3_interleave]
  simp [expressionValue, getElem!_pos, size, mul_eq,
    LeanCrypto.Groth16.FFT.mul,show LeanCrypto.Groth16.FFT.modulus=q from rfl]

end TornadoProofs.Witness.Primitive
#print axioms TornadoProofs.Witness.Primitive.coordinateExpressions_size
#print axioms TornadoProofs.Witness.Primitive.expression_get_value
#print axioms TornadoProofs.Witness.Primitive.coordinate_recipe
#print axioms TornadoProofs.Witness.Primitive.interleaveExpressions_value
#print axioms TornadoProofs.Witness.Primitive.primitiveExpressions_multiMux3
#print axioms TornadoProofs.Witness.Primitive.multiMux3_recipe

#print axioms TornadoProofs.Witness.Primitive.coordinateExpressions_actual
