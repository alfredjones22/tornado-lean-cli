import TornadoProofs.Witness.FeistelRowSupport

set_option autoImplicit false

namespace TornadoProofs.Witness.Local

open Tornado.Protocol.WitnessVM Tornado.Protocol.WitnessSymbolic
open LeanCrypto.Groth16.ConstraintCertificate LeanCrypto.Proofs.ConstraintCertificate
open LeanCrypto.Proofs.BN254Fr

abbrev RowsFrame := MProd Linear (MProd LocalSystem Linear)

def rowsRound (nodes : Array Node) (compiled : CompiledGraph) (constants : Array Nat)
    (stage : Feistel) (round : Nat) (frame : RowsFrame) : RowsFrame :=
  let row := signalLinear nodes compiled
  let left := frame.fst
  let system := frame.snd.fst
  let right := frame.snd.snd
  let t := sumLinear [left, row stage.key, constantLinear constants[round]!]
  let system := system.product stage.t2[round]! t t
  let system := system.product stage.t4[round]! (row stage.t2[round]!) (row stage.t2[round]!)
  if round < 219 then
    let system := system.constraint (row stage.t4[round]!) t (minusLinear (row stage.leftRounds[round]!) right)
    let system := system.equality stage.rightRounds[round]! left
    ⟨row stage.leftRounds[round]!, ⟨system, row stage.rightRounds[round]!⟩⟩
  else
    let system := system.equality stage.leftOutput left
    let system := system.constraint (row stage.t4[round]!) t (minusLinear (row stage.rightOutput) right)
    ⟨left, ⟨system, right⟩⟩

def rowsEffect (nodes : Array Node) (compiled : CompiledGraph) (constants : Array Nat)
    (stage : Feistel) (round : Nat) (frame : RowsFrame) : Id (ForInStep RowsFrame) :=
  let row := signalLinear nodes compiled
  let left := frame.fst
  let system := frame.snd.fst
  let right := frame.snd.snd
  let t := sumLinear [left, row stage.key, constantLinear constants[round]!]
  let system := system.product stage.t2[round]! t t
  let system := system.product stage.t4[round]! (row stage.t2[round]!) (row stage.t2[round]!)
  if round < 219 then
    let system := system.constraint (row stage.t4[round]!) t (minusLinear (row stage.leftRounds[round]!) right)
    let system := system.equality stage.rightRounds[round]! left
    pure (.yield ⟨row stage.leftRounds[round]!, ⟨system, row stage.rightRounds[round]!⟩⟩)
  else
    let system := system.equality stage.leftOutput left
    let system := system.constraint (row stage.t4[round]!) t (minusLinear (row stage.rightOutput) right)
    pure (.yield ⟨left, ⟨system, right⟩⟩)

theorem feistelLocalSystem_source (nodes : Array Node) (compiled : CompiledGraph) (constants : Array Nat)
    (system : LocalSystem) (stage : Feistel) :
    feistelLocalSystem nodes compiled constants system stage =
      ((List.range 220).foldl (fun frame round => rowsRound nodes compiled constants stage round frame)
        ⟨signalLinear nodes compiled stage.leftInput, ⟨system, signalLinear nodes compiled stage.rightInput⟩⟩).snd.fst := by
  unfold feistelLocalSystem
  change ((ForIn.forIn [0:220]
    (MProd.mk (signalLinear nodes compiled stage.leftInput) (MProd.mk system (signalLinear nodes compiled stage.rightInput)))
    (rowsEffect nodes compiled constants stage)) : Id RowsFrame).snd.fst = _
  have effect : rowsEffect nodes compiled constants stage =
      (fun round frame => (pure (.yield (rowsRound nodes compiled constants stage round frame)) : Id (ForInStep RowsFrame))) := by
    funext round frame
    unfold rowsEffect rowsRound
    split <;> rfl
  rw [effect]
  simp [List.range_eq_range']
  have projection (frame : RowsFrame) : (pure frame : Id RowsFrame).snd.fst = frame.snd.fst := rfl
  exact projection _

def FrameMeaning (assignment : Nat → Fr) (rows : RowsFrame) (native : FeistelFrame Assignment) : Prop :=
  linearValue assignment rows.fst = model native.left ∧
    linearValue assignment rows.snd.snd = model native.right

end TornadoProofs.Witness.Local

#print axioms TornadoProofs.Witness.Local.feistelLocalSystem_source
