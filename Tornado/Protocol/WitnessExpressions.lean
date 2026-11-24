import Tornado.Protocol.WitnessSymbolic

set_option autoImplicit false
namespace Tornado.Protocol.WitnessSymbolic

/-- Small public expression recipe. References are DAG node IDs, never witness
values. Compilation validates every returned node against its actual recipe. -/
inductive Expression where
  | reference (index : Nat)
  | constant (value : Nat)
  | bit (source : Expression) (position : Nat)
  | add (left right : Expression)
  | sub (left right : Expression)
  | mul (left right : Expression)
  | inverse (source : Expression)
  | select (selector left right : Expression)
  deriving Repr, Inhabited

def Expression.compile (resolver : Resolver) : Expression → Except String Nat
  | .reference index => pure index
  | .constant value => resolver.resolve (.constant value)
  | .bit source position => do
    resolver.resolve (.bit (← source.compile resolver) position)
  | .add left right => do
    resolver.resolve (.add (← left.compile resolver) (← right.compile resolver))
  | .sub left right => do
    resolver.resolve (.sub (← left.compile resolver) (← right.compile resolver))
  | .mul left right => do
    resolver.resolve (.mul (← left.compile resolver) (← right.compile resolver))
  | .inverse source => do
    resolver.resolve (.inverse (← source.compile resolver))
  | .select selector left right => do
    resolver.resolve (.select (← selector.compile resolver)
      (← left.compile resolver) (← right.compile resolver))

private def expressionCoordinate (inputs : Array Expression) (coordinate : Nat)
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

/-- Recipes mirror all actual VM arithmetic branches. Unsupported public kinds
produce no outputs and cannot satisfy the original shape checks. -/
def primitiveExpressions (kind : String) (inputIDs : Array Nat) : Array Expression := Id.run do
  let inputs := inputIDs.map Expression.reference
  match kind with
  | "MontgomeryAdd" =>
    let x1 := inputs[0]!; let y1 := inputs[1]!
    let x2 := inputs[2]!; let y2 := inputs[3]!
    let slope := .mul (.sub y2 y1) (.inverse (.sub x2 x1))
    let x := .sub (.sub (.sub (.mul slope slope) (.constant 168698)) x1) x2
    return #[slope,x,.sub (.mul slope (.sub x1 x)) y1]
  | "MontgomeryDouble" =>
    let x := inputs[0]!; let y := inputs[1]!
    let squared := .mul x x
    let numerator := .add (.add (.mul (.constant 3) squared) (.mul (.constant 337396) x)) (.constant 1)
    let slope := .mul numerator (.inverse (.mul (.constant 2) y))
    let outX := .sub (.sub (.mul slope slope) (.constant 168698)) (.mul (.constant 2) x)
    return #[squared,slope,outX,.sub (.mul slope (.sub x outX)) y]
  | "Edwards2Montgomery" =>
    let x := inputs[0]!; let y := inputs[1]!
    let outX := .mul (.add (.constant 1) y) (.inverse (.sub (.constant 1) y))
    return #[outX,.mul outX (.inverse x)]
  | "Montgomery2Edwards" =>
    let x := inputs[0]!; let y := inputs[1]!
    return #[.mul x (.inverse y),.mul (.sub x (.constant 1)) (.inverse (.add x (.constant 1)))]
  | "BabyAdd" =>
    let x1 := inputs[0]!; let y1 := inputs[1]!
    let x2 := inputs[2]!; let y2 := inputs[3]!
    let beta := .mul x1 y2; let gamma := .mul y1 x2
    let delta := .mul (.sub y1 (.mul (.constant 168700) x1)) (.add x2 y2)
    let tau := .mul beta gamma
    let x := .mul (.add beta gamma) (.inverse (.add (.constant 1) (.mul (.constant 168696) tau)))
    let y := .mul (.sub (.add delta (.mul (.constant 168700) beta)) gamma)
      (.inverse (.sub (.constant 1) (.mul (.constant 168696) tau)))
    return #[beta,gamma,delta,tau,x,y]
  | "Window4" =>
    return #[.sub inputs[0]! (.mul (.mul (.constant 2) inputs[0]!) inputs[1]!)]
  | "Square" => return #[.mul inputs[0]! inputs[0]!]
  | "MultiMux3" =>
    let s0 := inputs[0]!; let s1 := inputs[1]!; let s2 := inputs[2]!
    let s10 := Expression.mul s1 s0
    let a := expressionCoordinate inputs 0 s0 s1 s2 s10
    let b := expressionCoordinate inputs 1 s0 s1 s2 s10
    return #[s10,a[0]!,b[0]!,a[1]!,b[1]!,a[2]!,b[2]!,a[3]!,b[3]!,
      a[4]!,b[4]!,a[5]!,b[5]!,a[6]!,b[6]!,a[7]!,b[7]!,a[8]!,b[8]!]
  | _ => return #[]

def compilePrimitive (resolver : Resolver) (kind : String) (inputIDs : Array Nat) :
    Except String (Array Nat) :=
  (primitiveExpressions kind inputIDs).mapM (Expression.compile resolver)

end Tornado.Protocol.WitnessSymbolic
