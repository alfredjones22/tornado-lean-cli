import Tornado.Protocol.PedersenSchedule
import TornadoProofs.Witness.WindowSelection

set_option autoImplicit false
namespace TornadoProofs.Witness.PedersenReference
open Tornado.Protocol.PedersenSchedule
open Tornado.Protocol.WitnessSymbolic

structure WindowOps (m : Type → Type) (P B : Type) where
  doubled : P → m P
  added : P → P → m P
  bit : Nat → m B
  choose : B → B → B → Array P → m P
  signed : P → B → m P

def windowWith {m : Type → Type} [Monad m] {P B : Type} (ops : WindowOps m P B)
    (offset : Nat) (base : P) : m (P × P) := do
  let twice ← ops.doubled base
  let mut table := #[base,twice]
  let mut previous := twice
  for _ in [2:8] do
    previous ← ops.added base previous
    table := table.push previous
  let b0 ← ops.bit offset
  let b1 ← ops.bit (offset+1)
  let b2 ← ops.bit (offset+2)
  let sign ← ops.bit (offset+3)
  let chosen ← ops.choose b0 b1 b2 table
  let selected ← ops.signed chosen sign
  return (selected,previous)

structure ReferenceOps (m : Type → Type) (E P B : Type) where
  windows : WindowOps m P B
  toMontgomery : E → m P
  toEdwards : P → m E
  babyAdded : E → E → m E

def segmentWith {m : Type → Type} [Monad m] [MonadExceptOf String m] {E P B : Type}
    (ops : ReferenceOps m E P B) (offset windows : Nat) (base : E) : m E := do
  if windows == 0 then throw "Pedersen reference segment is empty."
  let converted ← ops.toMontgomery base
  let mut nextBase := converted
  let mut previousEight := nextBase
  let mut accumulator : Option P := none
  for index in [0:windows] do
    if index != 0 then
      let sixteen ← ops.windows.doubled previousEight
      nextBase ← ops.windows.doubled sixteen
    let (selected,eight) ← windowWith ops.windows (offset+4*index) nextBase
    previousEight := eight
    accumulator ← match accumulator with
      | none => pure (some selected)
      | some previous => some <$> ops.windows.added previous selected
  let some result := accumulator | throw "Pedersen reference has no segment result."
  ops.toEdwards result

def compilerWindows (resolver : Resolver) (commitment : Bool) : WindowOps Builder PointRef Nat where
  doubled := doubled resolver
  added := added resolver
  bit position := originalBit resolver commitment position
  choose b0 b1 b2 table := do
    let outputs ← operation resolver "MultiMux3" (#[b0,b1,b2] ++ table.map Prod.fst ++ table.map Prod.snd)
    return (outputs[17]!,outputs[18]!)
  signed point sign := do
    let outputs ← operation resolver "Window4" #[point.2,sign]
    return (point.1,outputs[0]!)

def compilerOps (resolver : Resolver) (commitment : Bool) : ReferenceOps Builder PointRef PointRef Nat where
  windows := compilerWindows resolver commitment
  toMontgomery point := do
    let converted ← operation resolver "Edwards2Montgomery" #[point.1,point.2]
    return (converted[0]!,converted[1]!)
  toEdwards point := do
    let converted ← operation resolver "Montgomery2Edwards" #[point.1,point.2]
    return (converted[0]!,converted[1]!)
  babyAdded := babyAdded resolver

theorem compiler_window_eq (resolver : Resolver) (commitment : Bool) (offset : Nat) (base : PointRef) :
    window resolver commitment offset base = windowWith (compilerWindows resolver commitment) offset base := by
  unfold window windowWith compilerWindows
  simp only [bind_pure_comp, bind_map_left, Functor.map_map]

def groupWindows {G : Type} [AddCommGroup G] [Inhabited G] (bits : Nat → Nat) : WindowOps (Except String) G Nat where
  doubled point := pure (point+point)
  added first second := pure (first+second)
  bit position := pure (bits position)
  choose b0 b1 b2 table := pure (table[PedersenWindows.selectorIndex b0 b1 b2]!)
  signed point sign := pure (if sign = 0 then point else -point)

def groupOps {G : Type} [AddCommGroup G] [Inhabited G] (bits : Nat → Nat) : ReferenceOps (Except String) G G Nat where
  windows := groupWindows bits
  toMontgomery := pure
  toEdwards := pure
  babyAdded first second := pure (first+second)

def programWith {m : Type → Type} [Monad m] [MonadExceptOf String m] {E P B : Type} [Inhabited E]
    (commitment nullifier : ReferenceOps m E P B) (bases : Array E) : m (E × E) := do
  if bases.size != 3 then throw "Pedersen reference requires three generators."
  let c0 ← segmentWith commitment 0 50 bases[0]!
  let c1 ← segmentWith commitment 200 50 bases[1]!
  let c2 ← segmentWith commitment 400 24 bases[2]!
  let first ← commitment.babyAdded c0 c1
  let commitmentPoint ← commitment.babyAdded first c2
  let n0 ← segmentWith nullifier 0 50 bases[0]!
  let n1 ← segmentWith nullifier 200 12 bases[1]!
  let nullifierPoint ← nullifier.babyAdded n0 n1
  return (commitmentPoint,nullifierPoint)

end TornadoProofs.Witness.PedersenReference
#print axioms TornadoProofs.Witness.PedersenReference.compiler_window_eq
