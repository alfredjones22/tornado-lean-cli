import TornadoProofs.Witness.SignalRows
import TornadoProofs.Witness.PrimitiveCompiler

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace TornadoProofs.Witness.Local
open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

def primitiveBody (nodes : Array Node) (compiled : CompiledGraph)
    (system : LocalSystem) (p : Tornado.Protocol.WitnessVM.Primitive) : Except String LocalSystem := do
  let row := signalLinear nodes compiled
  let input := p.inputs.map row
  let output := fun i => row p.outputs[i]!
  let x := input[0]?.getD []; let y := input[1]?.getD []
  let z := input[2]?.getD []; let w := input[3]?.getD []
  match p.kind with
  | "Square" => return system.product p.outputs[0]! x x
  | "MontgomeryAdd" =>
    return ((system.constraint (output 0) (minusLinear z x) (minusLinear w y)).constraint
      (output 0) (output 0) (sumLinear [output 1,constantLinear 168698,x,z])).constraint
      (output 0) (minusLinear x (output 1)) (addLinear (output 2) y)
  | "MontgomeryDouble" =>
    return (((system.product p.outputs[0]! x x).constraint (output 1) (scaleLinear 2 y)
      (sumLinear [scaleLinear 3 (output 0),scaleLinear 337396 x,constantLinear 1])).constraint
      (output 1) (output 1) (sumLinear [output 2,constantLinear 168698,scaleLinear 2 x])).constraint
      (output 1) (minusLinear x (output 2)) (addLinear (output 3) y)
  | "Edwards2Montgomery" =>
    return (system.constraint (output 0) (minusLinear (constantLinear 1) y)
      (addLinear (constantLinear 1) y)).constraint (output 1) x (output 0)
  | "Montgomery2Edwards" =>
    return (system.constraint (output 0) y x).constraint (output 1)
      (addLinear x (constantLinear 1)) (minusLinear x (constantLinear 1))
  | "BabyAdd" =>
    return (((((system.product p.outputs[0]! x w).product p.outputs[1]! y z).constraint
      (minusLinear y (scaleLinear 168700 x)) (addLinear z w) (output 2)).product
      p.outputs[3]! (output 0) (output 1)).constraint (output 4)
      (addLinear (constantLinear 1) (scaleLinear 168696 (output 3))) (addLinear (output 0) (output 1))).constraint
      (output 5) (minusLinear (constantLinear 1) (scaleLinear 168696 (output 3)))
      (minusLinear (addLinear (output 2) (scaleLinear 168700 (output 0))) (output 1))
  | "Window4" =>
    return system.constraint (scaleLinear 2 x) y (minusLinear x (output 0))
  | "MultiMux3" =>
    let mut result := system.product p.outputs[0]! input[1]! input[0]!
    for coordinate in [0:2] do
      let c := fun i => input[3+coordinate*8+i]!
      let index := fun i => p.outputs[1+i*2+coordinate]!
      let out := fun i => row (index i)
      let a210 := sumLinear [c 7,negLinear (c 6),negLinear (c 5),c 4,
        negLinear (c 3),c 2,c 1,negLinear (c 0)]
      result := result.product (index 0) a210 (output 0)
      result := result.product (index 1) (sumLinear [c 6,negLinear (c 4),negLinear (c 2),c 0]) input[1]!
      result := result.product (index 2) (sumLinear [c 5,negLinear (c 4),negLinear (c 1),c 0]) input[0]!
      result := result.equality (index 3) (minusLinear (c 4) (c 0))
      result := result.product (index 4) (sumLinear [c 3,negLinear (c 2),negLinear (c 1),c 0]) (output 0)
      result := result.product (index 5) (minusLinear (c 2) (c 0)) input[1]!
      result := result.product (index 6) (minusLinear (c 1) (c 0)) input[0]!
      result := result.equality (index 7) (c 0)
      result := result.constraint (sumLinear [out 0,out 1,out 2,out 3]) input[2]!
        (minusLinear (out 8) (sumLinear [out 4,out 5,out 6,c 0]))
    return result
  | _ => throw "Public witness local constraint kind is unsupported."

def constantRowEffect (nodes : Array Node) (compiled : CompiledGraph)
    (index : Nat) (system : LocalSystem) : Except String (ForInStep LocalSystem) := do
  match constantAt nodes compiled.signalRoots[index]! with
  | none => pure (.yield system)
  | some value => pure (.yield (system.equality index (constantLinear value)))

theorem primitiveLocalSystem_source (nodes : Array Node) (compiled : CompiledGraph)
    (system : LocalSystem) (p : Tornado.Protocol.WitnessVM.Primitive) :
    primitiveLocalSystem nodes compiled system p = (do
      let accumulated ← forIn p.outputs.toList system (constantRowEffect nodes compiled)
      primitiveBody nodes compiled accumulated p) := by
  unfold primitiveLocalSystem primitiveBody
  rw [Array.forIn_toList]
  rfl

end TornadoProofs.Witness.Local
#print axioms TornadoProofs.Witness.Local.primitiveLocalSystem_source
